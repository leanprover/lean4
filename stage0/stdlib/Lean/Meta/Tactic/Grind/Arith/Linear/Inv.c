// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Inv
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.Linear.Util
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___boxed(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.Grind.Arith.Linear.Inv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.0.Lean.Grind.Linarith.Poly.checkOccs.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 123, .m_capacity = 123, .m_length = 122, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.2982430543._hygCtx._hyg.65.0 ).contains y\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.0.Lean.Grind.Linarith.Poly.checkNoElimVars"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "assertion violation: !( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.341169003._hygCtx._hyg.33.0 )\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.0.Lean.Grind.Linarith.Poly.checkCnstrOf"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "assertion violation: x == y\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: p.isSorted\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: p.checkCoeffs\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.0.Lean.Meta.Grind.Arith.Linear.checkLeCnstrs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: isLower == (a < 0)\n    "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.0.Lean.Meta.Grind.Arith.Linear.checkLowers"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: s.lowers.size == s.vars.size\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.0.Lean.Meta.Grind.Arith.Linear.checkUppers"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: s.uppers.size == s.vars.size\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.0.Lean.Meta.Grind.Arith.Linear.checkDiseqCnstrs"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: s.vars.size == s.diseqs.size\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.0.Lean.Meta.Grind.Arith.Linear.checkVars"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "assertion violation: isSameExpr expr expr'\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: s.vars.size == num\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Meta.Grind.Arith.Linear.checkInvariants"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.3119225764._hygCtx._hyg.60.0 ) == structId\n      "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___boxed(lean_object**);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
uint8_t v___x_3_; 
lean_dec(v_a_1_);
v___x_3_ = 1;
return v___x_3_;
}
else
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v_v_4_; lean_object* v_p_5_; lean_object* v___x_6_; 
v_v_4_ = lean_ctor_get(v_a_2_, 1);
v_p_5_ = lean_ctor_get(v_a_2_, 2);
lean_inc(v_v_4_);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_v_4_);
v_a_1_ = v___x_6_;
v_a_2_ = v_p_5_;
goto _start;
}
else
{
lean_object* v_v_8_; lean_object* v_p_9_; lean_object* v_val_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_19_; 
v_v_8_ = lean_ctor_get(v_a_2_, 1);
v_p_9_ = lean_ctor_get(v_a_2_, 2);
v_val_10_ = lean_ctor_get(v_a_1_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_19_ == 0)
{
v___x_12_ = v_a_1_;
v_isShared_13_ = v_isSharedCheck_19_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_val_10_);
lean_dec(v_a_1_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_19_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_lt(v_v_8_, v_val_10_);
lean_dec(v_val_10_);
if (v___x_14_ == 0)
{
lean_del_object(v___x_12_);
return v___x_14_;
}
else
{
lean_object* v___x_16_; 
lean_inc(v_v_8_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v_v_8_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_v_8_);
v___x_16_ = v_reuseFailAlloc_18_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
v_a_1_ = v___x_16_;
v_a_2_ = v_p_9_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go___boxed(lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(v_a_20_, v_a_21_);
lean_dec(v_a_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(lean_object* v_p_24_){
_start:
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_box(0);
v___x_26_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(v___x_25_, v_p_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted___boxed(lean_object* v_p_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(v_p_27_);
lean_dec(v_p_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_to_int(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
uint8_t v___x_33_; 
v___x_33_ = 1;
return v___x_33_;
}
else
{
lean_object* v_k_34_; lean_object* v_p_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_k_34_ = lean_ctor_get(v_x_32_, 0);
v_p_35_ = lean_ctor_get(v_x_32_, 2);
v___x_36_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_37_ = lean_int_dec_eq(v_k_34_, v___x_36_);
if (v___x_37_ == 0)
{
v_x_32_ = v_p_35_;
goto _start;
}
else
{
uint8_t v___x_39_; 
v___x_39_ = 0;
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___boxed(lean_object* v_x_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(v_x_40_);
lean_dec(v_x_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(lean_object* v_msg_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v___f_58_; lean_object* v___x_1769__overap_59_; lean_object* v___x_60_; 
v___x_57_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0);
v___f_58_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_58_, 0, v___x_57_);
v___x_1769__overap_59_ = lean_panic_fn_borrowed(v___f_58_, v_msg_44_);
lean_dec_ref(v___f_58_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
lean_inc(v___y_51_);
lean_inc_ref(v___y_50_);
lean_inc(v___y_49_);
lean_inc_ref(v___y_48_);
lean_inc(v___y_47_);
lean_inc(v___y_46_);
lean_inc(v___y_45_);
v___x_60_ = lean_apply_12(v___x_1769__overap_59_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, lean_box(0));
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___boxed(lean_object* v_msg_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v_msg_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec(v___y_63_);
lean_dec(v___y_62_);
return v_res_74_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(lean_object* v_k_75_, lean_object* v_t_76_){
_start:
{
if (lean_obj_tag(v_t_76_) == 0)
{
lean_object* v_k_77_; lean_object* v_l_78_; lean_object* v_r_79_; uint8_t v___x_80_; 
v_k_77_ = lean_ctor_get(v_t_76_, 1);
v_l_78_ = lean_ctor_get(v_t_76_, 3);
v_r_79_ = lean_ctor_get(v_t_76_, 4);
v___x_80_ = lean_nat_dec_lt(v_k_75_, v_k_77_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = lean_nat_dec_eq(v_k_75_, v_k_77_);
if (v___x_81_ == 0)
{
v_t_76_ = v_r_79_;
goto _start;
}
else
{
return v___x_81_;
}
}
else
{
v_t_76_ = v_l_78_;
goto _start;
}
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg___boxed(lean_object* v_k_85_, lean_object* v_t_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_k_85_, v_t_86_);
lean_dec(v_t_86_);
lean_dec(v_k_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2));
v___x_93_ = lean_unsigned_to_nat(4u);
v___x_94_ = lean_unsigned_to_nat(32u);
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1));
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_97_ = l_mkPanicMessageWithDecl(v___x_96_, v___x_95_, v___x_94_, v___x_93_, v___x_92_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(lean_object* v_y_98_, lean_object* v_p_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
if (lean_obj_tag(v_p_99_) == 1)
{
lean_object* v_v_112_; lean_object* v_p_113_; lean_object* v___x_114_; 
v_v_112_ = lean_ctor_get(v_p_99_, 1);
v_p_113_ = lean_ctor_get(v_p_99_, 2);
v___x_114_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_v_112_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; uint8_t v___x_116_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_a_115_);
lean_dec_ref_known(v___x_114_, 1);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_y_98_, v_a_115_);
lean_dec(v_a_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3);
v___x_118_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_117_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_118_;
}
else
{
v_p_99_ = v_p_113_;
goto _start;
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_114_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_114_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___boxed(lean_object* v_y_130_, lean_object* v_p_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(v_y_130_, v_p_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec(v_a_133_);
lean_dec(v_a_132_);
lean_dec(v_p_131_);
lean_dec(v_y_130_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(lean_object* v_00_u03b2_145_, lean_object* v_k_146_, lean_object* v_t_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_k_146_, v_t_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___boxed(lean_object* v_00_u03b2_149_, lean_object* v_k_150_, lean_object* v_t_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(v_00_u03b2_149_, v_k_150_, v_t_151_);
lean_dec(v_t_151_);
lean_dec(v_k_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(lean_object* v_p_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
if (lean_obj_tag(v_p_154_) == 1)
{
lean_object* v_v_167_; lean_object* v_p_168_; lean_object* v___x_169_; 
v_v_167_ = lean_ctor_get(v_p_154_, 1);
v_p_168_ = lean_ctor_get(v_p_154_, 2);
v___x_169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(v_v_167_, v_p_168_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_box(0);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs___boxed(lean_object* v_p_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(v_p_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec(v_a_174_);
lean_dec(v_a_173_);
lean_dec(v_p_172_);
return v_res_185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1));
v___x_189_ = lean_unsigned_to_nat(2u);
v___x_190_ = lean_unsigned_to_nat(38u);
v___x_191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0));
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_193_ = l_mkPanicMessageWithDecl(v___x_192_, v___x_191_, v___x_190_, v___x_189_, v___x_188_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(lean_object* v_p_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
if (lean_obj_tag(v_p_194_) == 1)
{
lean_object* v_v_207_; lean_object* v_p_208_; lean_object* v___x_209_; 
v_v_207_ = lean_ctor_get(v_p_194_, 1);
v_p_208_ = lean_ctor_get(v_p_194_, 2);
v___x_209_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_v_207_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; uint8_t v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = lean_unbox(v_a_210_);
lean_dec(v_a_210_);
if (v___x_211_ == 0)
{
v_p_194_ = v_p_208_;
goto _start;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2);
v___x_214_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_213_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_214_;
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_a_215_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_209_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_209_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_box(0);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___boxed(lean_object* v_p_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec(v_a_227_);
lean_dec(v_a_226_);
lean_dec(v_p_225_);
return v_res_238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1));
v___x_242_ = lean_unsigned_to_nat(2u);
v___x_243_ = lean_unsigned_to_nat(49u);
v___x_244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0));
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_246_ = l_mkPanicMessageWithDecl(v___x_245_, v___x_244_, v___x_243_, v___x_242_, v___x_241_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3));
v___x_249_ = lean_unsigned_to_nat(24u);
v___x_250_ = lean_unsigned_to_nat(48u);
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0));
v___x_252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_253_ = l_mkPanicMessageWithDecl(v___x_252_, v___x_251_, v___x_250_, v___x_249_, v___x_248_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5));
v___x_256_ = lean_unsigned_to_nat(2u);
v___x_257_ = lean_unsigned_to_nat(42u);
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0));
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_260_ = l_mkPanicMessageWithDecl(v___x_259_, v___x_258_, v___x_257_, v___x_256_, v___x_255_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7));
v___x_263_ = lean_unsigned_to_nat(2u);
v___x_264_ = lean_unsigned_to_nat(43u);
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0));
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_267_ = l_mkPanicMessageWithDecl(v___x_266_, v___x_265_, v___x_264_, v___x_263_, v___x_262_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(lean_object* v_p_268_, lean_object* v_x_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; uint8_t v___x_302_; 
v___x_302_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(v_p_268_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6);
v___x_304_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_303_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v___x_304_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(v_p_268_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8);
v___x_307_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_306_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; uint8_t v___x_310_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_308_, 1);
v___x_310_ = lean_unbox(v_a_309_);
lean_dec(v_a_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_268_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_312_; 
lean_dec_ref_known(v___x_311_, 1);
v___x_312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(v_p_268_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_dec_ref_known(v___x_312_, 1);
v___y_283_ = v_a_270_;
v___y_284_ = v_a_271_;
v___y_285_ = v_a_272_;
v___y_286_ = v_a_273_;
v___y_287_ = v_a_274_;
v___y_288_ = v_a_275_;
v___y_289_ = v_a_276_;
v___y_290_ = v_a_277_;
v___y_291_ = v_a_278_;
v___y_292_ = v_a_279_;
v___y_293_ = v_a_280_;
goto v___jp_282_;
}
else
{
return v___x_312_;
}
}
else
{
return v___x_311_;
}
}
else
{
v___y_283_ = v_a_270_;
v___y_284_ = v_a_271_;
v___y_285_ = v_a_272_;
v___y_286_ = v_a_273_;
v___y_287_ = v_a_274_;
v___y_288_ = v_a_275_;
v___y_289_ = v_a_276_;
v___y_290_ = v_a_277_;
v___y_291_ = v_a_278_;
v___y_292_ = v_a_279_;
v___y_293_ = v_a_280_;
goto v___jp_282_;
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_313_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_308_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_308_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
v___jp_282_:
{
if (lean_obj_tag(v_p_268_) == 1)
{
lean_object* v_v_294_; uint8_t v___x_295_; 
v_v_294_ = lean_ctor_get(v_p_268_, 1);
v___x_295_ = lean_nat_dec_eq(v_x_269_, v_v_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2);
v___x_297_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_296_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_box(0);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4);
v___x_301_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_300_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___boxed(lean_object* v_p_321_, lean_object* v_x_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_321_, v_x_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec(v_x_322_);
lean_dec(v_p_321_);
return v_res_335_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___f_351_; lean_object* v___x_4372__overap_352_; lean_object* v___x_353_; 
v___x_350_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0);
v___f_351_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_351_, 0, v___x_350_);
v___x_4372__overap_352_ = lean_panic_fn_borrowed(v___f_351_, v_msg_337_);
lean_dec_ref(v___f_351_);
lean_inc(v___y_348_);
lean_inc_ref(v___y_347_);
lean_inc(v___y_346_);
lean_inc_ref(v___y_345_);
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
lean_inc(v___y_342_);
lean_inc_ref(v___y_341_);
lean_inc(v___y_340_);
lean_inc(v___y_339_);
lean_inc(v___y_338_);
v___x_353_ = lean_apply_12(v___x_4372__overap_352_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, lean_box(0));
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___boxed(lean_object* v_msg_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v_msg_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec(v___y_356_);
lean_dec(v___y_355_);
return v_res_367_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1));
v___x_371_ = lean_unsigned_to_nat(6u);
v___x_372_ = lean_unsigned_to_nat(57u);
v___x_373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0));
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_375_ = l_mkPanicMessageWithDecl(v___x_374_, v___x_373_, v___x_372_, v___x_371_, v___x_370_);
return v___x_375_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3));
v___x_377_ = lean_unsigned_to_nat(30u);
v___x_378_ = lean_unsigned_to_nat(56u);
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0));
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_381_ = l_mkPanicMessageWithDecl(v___x_380_, v___x_379_, v___x_378_, v___x_377_, v___x_376_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object* v_____s_382_, uint8_t v_isLower_383_, lean_object* v_as_384_, size_t v_sz_385_, size_t v_i_386_, lean_object* v_b_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_lt(v_i_386_, v_sz_385_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v_b_387_);
return v___x_401_;
}
else
{
lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_463_; 
v_snd_402_ = lean_ctor_get(v_b_387_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_b_387_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v_b_387_, 0);
lean_dec(v_unused_464_);
v___x_404_ = v_b_387_;
v_isShared_405_ = v_isSharedCheck_463_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_dec(v_b_387_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_463_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_a_406_; lean_object* v_p_407_; lean_object* v___x_408_; 
v_a_406_ = lean_array_uget_borrowed(v_as_384_, v_i_386_);
v_p_407_ = lean_ctor_get(v_a_406_, 0);
v___x_408_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_407_, v_____s_382_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_409_; lean_object* v_a_411_; lean_object* v___x_418_; uint8_t v___y_420_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_409_ = lean_box(0);
v___x_418_ = lean_box(0);
if (lean_obj_tag(v_p_407_) == 1)
{
lean_object* v_k_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_k_442_ = lean_ctor_get(v_p_407_, 0);
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_444_ = lean_int_dec_lt(v_k_442_, v___x_443_);
if (v___x_444_ == 0)
{
if (v_isLower_383_ == 0)
{
v___y_420_ = v___x_400_;
goto v___jp_419_;
}
else
{
v___y_420_ = v___x_444_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_isLower_383_;
goto v___jp_419_;
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_snd_402_);
v___x_445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_446_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_445_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_dec_ref_known(v___x_446_, 1);
v_a_411_ = v___x_418_;
goto v___jp_410_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_del_object(v___x_404_);
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
v___jp_410_:
{
lean_object* v___x_413_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_a_411_);
lean_ctor_set(v___x_404_, 0, v___x_409_);
v___x_413_ = v___x_404_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_a_411_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
size_t v___x_414_; size_t v___x_415_; 
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_386_, v___x_414_);
v_i_386_ = v___x_415_;
v_b_387_ = v___x_413_;
goto _start;
}
}
v___jp_419_:
{
if (v___y_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_422_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_421_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_433_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_433_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
if (lean_obj_tag(v_a_423_) == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
lean_del_object(v___x_404_);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_a_423_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_snd_402_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_428_);
v___x_430_ = v___x_425_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
lean_object* v_a_432_; 
lean_del_object(v___x_425_);
lean_dec(v_snd_402_);
v_a_432_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v_a_423_, 1);
v_a_411_ = v_a_432_;
goto v___jp_410_;
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
v_a_434_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_422_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_422_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_dec(v_snd_402_);
v_a_411_ = v___x_418_;
goto v___jp_410_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
v_a_455_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_408_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_408_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_____s_465_ = _args[0];
lean_object* v_isLower_466_ = _args[1];
lean_object* v_as_467_ = _args[2];
lean_object* v_sz_468_ = _args[3];
lean_object* v_i_469_ = _args[4];
lean_object* v_b_470_ = _args[5];
lean_object* v___y_471_ = _args[6];
lean_object* v___y_472_ = _args[7];
lean_object* v___y_473_ = _args[8];
lean_object* v___y_474_ = _args[9];
lean_object* v___y_475_ = _args[10];
lean_object* v___y_476_ = _args[11];
lean_object* v___y_477_ = _args[12];
lean_object* v___y_478_ = _args[13];
lean_object* v___y_479_ = _args[14];
lean_object* v___y_480_ = _args[15];
lean_object* v___y_481_ = _args[16];
lean_object* v___y_482_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_483_; size_t v_sz_boxed_484_; size_t v_i_boxed_485_; lean_object* v_res_486_; 
v_isLower_boxed_483_ = lean_unbox(v_isLower_466_);
v_sz_boxed_484_ = lean_unbox_usize(v_sz_468_);
lean_dec(v_sz_468_);
v_i_boxed_485_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_res_486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_465_, v_isLower_boxed_483_, v_as_467_, v_sz_boxed_484_, v_i_boxed_485_, v_b_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v_as_467_);
lean_dec(v_____s_465_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object* v_____s_487_, uint8_t v_isLower_488_, lean_object* v_as_489_, size_t v_sz_490_, size_t v_i_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_lt(v_i_491_, v_sz_490_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v_b_492_);
return v___x_506_;
}
else
{
lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_568_; 
v_snd_507_ = lean_ctor_get(v_b_492_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_b_492_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v_b_492_, 0);
lean_dec(v_unused_569_);
v___x_509_ = v_b_492_;
v_isShared_510_ = v_isSharedCheck_568_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_dec(v_b_492_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_568_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_a_511_; lean_object* v_p_512_; lean_object* v___x_513_; 
v_a_511_ = lean_array_uget_borrowed(v_as_489_, v_i_491_);
v_p_512_ = lean_ctor_get(v_a_511_, 0);
v___x_513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_512_, v_____s_487_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_a_517_; uint8_t v___y_525_; 
lean_dec_ref_known(v___x_513_, 1);
v___x_514_ = lean_box(0);
v___x_515_ = lean_box(0);
if (lean_obj_tag(v_p_512_) == 1)
{
lean_object* v_k_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_k_547_ = lean_ctor_get(v_p_512_, 0);
v___x_548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_549_ = lean_int_dec_lt(v_k_547_, v___x_548_);
if (v___x_549_ == 0)
{
if (v_isLower_488_ == 0)
{
v___y_525_ = v___x_505_;
goto v___jp_524_;
}
else
{
v___y_525_ = v___x_549_;
goto v___jp_524_;
}
}
else
{
v___y_525_ = v_isLower_488_;
goto v___jp_524_;
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v_snd_507_);
v___x_550_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_551_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_550_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_dec_ref_known(v___x_551_, 1);
v_a_517_ = v___x_514_;
goto v___jp_516_;
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_del_object(v___x_509_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
v___jp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_a_517_);
lean_ctor_set(v___x_509_, 0, v___x_515_);
v___x_519_ = v___x_509_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_a_517_);
v___x_519_ = v_reuseFailAlloc_523_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_add(v_i_491_, v___x_520_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_487_, v_isLower_488_, v_as_489_, v_sz_490_, v___x_521_, v___x_519_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_522_;
}
}
v___jp_524_:
{
if (v___y_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_527_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_526_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_538_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_538_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_538_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_538_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
if (lean_obj_tag(v_a_528_) == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
lean_del_object(v___x_509_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v_a_528_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_snd_507_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_533_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v_a_537_; 
lean_del_object(v___x_530_);
lean_dec(v_snd_507_);
v_a_537_ = lean_ctor_get(v_a_528_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v_a_528_, 1);
v_a_517_ = v_a_537_;
goto v___jp_516_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
v_a_539_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_527_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_527_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_dec(v_snd_507_);
v_a_517_ = v___x_514_;
goto v___jp_516_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
v_a_560_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_513_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_513_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_____s_570_ = _args[0];
lean_object* v_isLower_571_ = _args[1];
lean_object* v_as_572_ = _args[2];
lean_object* v_sz_573_ = _args[3];
lean_object* v_i_574_ = _args[4];
lean_object* v_b_575_ = _args[5];
lean_object* v___y_576_ = _args[6];
lean_object* v___y_577_ = _args[7];
lean_object* v___y_578_ = _args[8];
lean_object* v___y_579_ = _args[9];
lean_object* v___y_580_ = _args[10];
lean_object* v___y_581_ = _args[11];
lean_object* v___y_582_ = _args[12];
lean_object* v___y_583_ = _args[13];
lean_object* v___y_584_ = _args[14];
lean_object* v___y_585_ = _args[15];
lean_object* v___y_586_ = _args[16];
lean_object* v___y_587_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_588_; size_t v_sz_boxed_589_; size_t v_i_boxed_590_; lean_object* v_res_591_; 
v_isLower_boxed_588_ = lean_unbox(v_isLower_571_);
v_sz_boxed_589_ = lean_unbox_usize(v_sz_573_);
lean_dec(v_sz_573_);
v_i_boxed_590_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_570_, v_isLower_boxed_588_, v_as_572_, v_sz_boxed_589_, v_i_boxed_590_, v_b_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v_as_572_);
lean_dec(v_____s_570_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(lean_object* v_init_592_, lean_object* v_____s_593_, uint8_t v_isLower_594_, lean_object* v_n_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
if (lean_obj_tag(v_n_595_) == 0)
{
lean_object* v_cs_609_; lean_object* v___x_610_; lean_object* v___x_611_; size_t v_sz_612_; size_t v___x_613_; lean_object* v___x_614_; 
v_cs_609_ = lean_ctor_get(v_n_595_, 0);
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v_b_596_);
v_sz_612_ = lean_array_size(v_cs_609_);
v___x_613_ = ((size_t)0ULL);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_592_, v_____s_593_, v_isLower_594_, v_cs_609_, v_sz_612_, v___x_613_, v___x_611_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_629_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_629_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_fst_619_; 
v_fst_619_ = lean_ctor_get(v_a_615_, 0);
if (lean_obj_tag(v_fst_619_) == 0)
{
lean_object* v_snd_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v_snd_620_ = lean_ctor_get(v_a_615_, 1);
lean_inc(v_snd_620_);
lean_dec(v_a_615_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v_snd_620_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_621_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v_val_625_; lean_object* v___x_627_; 
lean_inc_ref(v_fst_619_);
lean_dec(v_a_615_);
v_val_625_ = lean_ctor_get(v_fst_619_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v_fst_619_, 1);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_val_625_);
v___x_627_ = v___x_617_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_val_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_614_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_614_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_vs_638_; lean_object* v___x_639_; lean_object* v___x_640_; size_t v_sz_641_; size_t v___x_642_; lean_object* v___x_643_; 
v_vs_638_ = lean_ctor_get(v_n_595_, 0);
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_b_596_);
v_sz_641_ = lean_array_size(v_vs_638_);
v___x_642_ = ((size_t)0ULL);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_593_, v_isLower_594_, v_vs_638_, v_sz_641_, v___x_642_, v___x_640_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_658_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_658_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_658_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_658_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_fst_648_; 
v_fst_648_ = lean_ctor_get(v_a_644_, 0);
if (lean_obj_tag(v_fst_648_) == 0)
{
lean_object* v_snd_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v_snd_649_ = lean_ctor_get(v_a_644_, 1);
lean_inc(v_snd_649_);
lean_dec(v_a_644_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v_snd_649_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_650_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v_val_654_; lean_object* v___x_656_; 
lean_inc_ref(v_fst_648_);
lean_dec(v_a_644_);
v_val_654_ = lean_ctor_get(v_fst_648_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v_fst_648_, 1);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v_val_654_);
v___x_656_ = v___x_646_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_val_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_643_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_643_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_init_667_, lean_object* v_____s_668_, uint8_t v_isLower_669_, lean_object* v_as_670_, size_t v_sz_671_, size_t v_i_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_lt(v_i_672_, v_sz_671_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v_b_673_);
return v___x_687_;
}
else
{
lean_object* v_snd_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_722_; 
v_snd_688_ = lean_ctor_get(v_b_673_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_b_673_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_b_673_, 0);
lean_dec(v_unused_723_);
v___x_690_ = v_b_673_;
v_isShared_691_ = v_isSharedCheck_722_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snd_688_);
lean_dec(v_b_673_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_722_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_a_692_; lean_object* v___x_693_; 
v_a_692_ = lean_array_uget_borrowed(v_as_670_, v_i_672_);
lean_inc(v_snd_688_);
v___x_693_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_667_, v_____s_668_, v_isLower_669_, v_a_692_, v_snd_688_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_713_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_713_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_713_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_713_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
if (lean_obj_tag(v_a_694_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v_a_694_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_698_);
v___x_700_ = v___x_690_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_snd_688_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_700_);
v___x_702_ = v___x_696_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
lean_del_object(v___x_696_);
lean_dec(v_snd_688_);
v_a_705_ = lean_ctor_get(v_a_694_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v_a_694_, 1);
v___x_706_ = lean_box(0);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_a_705_);
lean_ctor_set(v___x_690_, 0, v___x_706_);
v___x_708_ = v___x_690_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_a_705_);
v___x_708_ = v_reuseFailAlloc_712_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
size_t v___x_709_; size_t v___x_710_; 
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_add(v_i_672_, v___x_709_);
v_i_672_ = v___x_710_;
v_b_673_ = v___x_708_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_del_object(v___x_690_);
lean_dec(v_snd_688_);
v_a_714_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_693_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_693_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_724_ = _args[0];
lean_object* v_____s_725_ = _args[1];
lean_object* v_isLower_726_ = _args[2];
lean_object* v_as_727_ = _args[3];
lean_object* v_sz_728_ = _args[4];
lean_object* v_i_729_ = _args[5];
lean_object* v_b_730_ = _args[6];
lean_object* v___y_731_ = _args[7];
lean_object* v___y_732_ = _args[8];
lean_object* v___y_733_ = _args[9];
lean_object* v___y_734_ = _args[10];
lean_object* v___y_735_ = _args[11];
lean_object* v___y_736_ = _args[12];
lean_object* v___y_737_ = _args[13];
lean_object* v___y_738_ = _args[14];
lean_object* v___y_739_ = _args[15];
lean_object* v___y_740_ = _args[16];
lean_object* v___y_741_ = _args[17];
lean_object* v___y_742_ = _args[18];
_start:
{
uint8_t v_isLower_boxed_743_; size_t v_sz_boxed_744_; size_t v_i_boxed_745_; lean_object* v_res_746_; 
v_isLower_boxed_743_ = lean_unbox(v_isLower_726_);
v_sz_boxed_744_ = lean_unbox_usize(v_sz_728_);
lean_dec(v_sz_728_);
v_i_boxed_745_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_724_, v_____s_725_, v_isLower_boxed_743_, v_as_727_, v_sz_boxed_744_, v_i_boxed_745_, v_b_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v_as_727_);
lean_dec(v_____s_725_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_init_747_ = _args[0];
lean_object* v_____s_748_ = _args[1];
lean_object* v_isLower_749_ = _args[2];
lean_object* v_n_750_ = _args[3];
lean_object* v_b_751_ = _args[4];
lean_object* v___y_752_ = _args[5];
lean_object* v___y_753_ = _args[6];
lean_object* v___y_754_ = _args[7];
lean_object* v___y_755_ = _args[8];
lean_object* v___y_756_ = _args[9];
lean_object* v___y_757_ = _args[10];
lean_object* v___y_758_ = _args[11];
lean_object* v___y_759_ = _args[12];
lean_object* v___y_760_ = _args[13];
lean_object* v___y_761_ = _args[14];
lean_object* v___y_762_ = _args[15];
lean_object* v___y_763_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_764_; lean_object* v_res_765_; 
v_isLower_boxed_764_ = lean_unbox(v_isLower_749_);
v_res_765_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_747_, v_____s_748_, v_isLower_boxed_764_, v_n_750_, v_b_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v_n_750_);
lean_dec(v_____s_748_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object* v_____s_766_, uint8_t v_isLower_767_, lean_object* v_as_768_, size_t v_sz_769_, size_t v_i_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = lean_usize_dec_lt(v_i_770_, v_sz_769_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v_b_771_);
return v___x_785_;
}
else
{
lean_object* v_snd_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_854_; 
v_snd_786_ = lean_ctor_get(v_b_771_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_b_771_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_b_771_, 0);
lean_dec(v_unused_855_);
v___x_788_ = v_b_771_;
v_isShared_789_ = v_isSharedCheck_854_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snd_786_);
lean_dec(v_b_771_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_854_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_a_790_; lean_object* v_p_791_; lean_object* v___x_792_; 
v_a_790_ = lean_array_uget_borrowed(v_as_768_, v_i_770_);
v_p_791_ = lean_ctor_get(v_a_790_, 0);
v___x_792_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_791_, v_____s_766_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; lean_object* v_a_795_; lean_object* v___x_802_; uint8_t v___y_804_; 
lean_dec_ref_known(v___x_792_, 1);
v___x_793_ = lean_box(0);
v___x_802_ = lean_box(0);
if (lean_obj_tag(v_p_791_) == 1)
{
lean_object* v_k_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_k_833_ = lean_ctor_get(v_p_791_, 0);
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_835_ = lean_int_dec_lt(v_k_833_, v___x_834_);
if (v___x_835_ == 0)
{
if (v_isLower_767_ == 0)
{
v___y_804_ = v___x_784_;
goto v___jp_803_;
}
else
{
v___y_804_ = v___x_835_;
goto v___jp_803_;
}
}
else
{
v___y_804_ = v_isLower_767_;
goto v___jp_803_;
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_snd_786_);
v___x_836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_837_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_836_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_dec_ref_known(v___x_837_, 1);
v_a_795_ = v___x_802_;
goto v___jp_794_;
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_del_object(v___x_788_);
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
v___jp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v_a_795_);
lean_ctor_set(v___x_788_, 0, v___x_793_);
v___x_797_ = v___x_788_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_a_795_);
v___x_797_ = v_reuseFailAlloc_801_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
size_t v___x_798_; size_t v___x_799_; 
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_i_770_, v___x_798_);
v_i_770_ = v___x_799_;
v_b_771_ = v___x_797_;
goto _start;
}
}
v___jp_803_:
{
if (v___y_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_806_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_805_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_824_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_824_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
if (lean_obj_tag(v_a_807_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_822_; 
lean_del_object(v___x_788_);
v_a_811_ = lean_ctor_get(v_a_807_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_a_807_);
if (v_isSharedCheck_822_ == 0)
{
v___x_813_ = v_a_807_;
v_isShared_814_ = v_isSharedCheck_822_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v_a_807_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_822_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 1);
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_821_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_snd_786_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_817_);
v___x_819_ = v___x_809_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_a_823_; 
lean_del_object(v___x_809_);
lean_dec(v_snd_786_);
v_a_823_ = lean_ctor_get(v_a_807_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v_a_807_, 1);
v_a_795_ = v_a_823_;
goto v___jp_794_;
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_del_object(v___x_788_);
lean_dec(v_snd_786_);
v_a_825_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_806_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_806_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_dec(v_snd_786_);
v_a_795_ = v___x_802_;
goto v___jp_794_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_del_object(v___x_788_);
lean_dec(v_snd_786_);
v_a_846_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_792_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_792_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_____s_856_ = _args[0];
lean_object* v_isLower_857_ = _args[1];
lean_object* v_as_858_ = _args[2];
lean_object* v_sz_859_ = _args[3];
lean_object* v_i_860_ = _args[4];
lean_object* v_b_861_ = _args[5];
lean_object* v___y_862_ = _args[6];
lean_object* v___y_863_ = _args[7];
lean_object* v___y_864_ = _args[8];
lean_object* v___y_865_ = _args[9];
lean_object* v___y_866_ = _args[10];
lean_object* v___y_867_ = _args[11];
lean_object* v___y_868_ = _args[12];
lean_object* v___y_869_ = _args[13];
lean_object* v___y_870_ = _args[14];
lean_object* v___y_871_ = _args[15];
lean_object* v___y_872_ = _args[16];
lean_object* v___y_873_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_874_; size_t v_sz_boxed_875_; size_t v_i_boxed_876_; lean_object* v_res_877_; 
v_isLower_boxed_874_ = lean_unbox(v_isLower_857_);
v_sz_boxed_875_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_876_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_856_, v_isLower_boxed_874_, v_as_858_, v_sz_boxed_875_, v_i_boxed_876_, v_b_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v_as_858_);
lean_dec(v_____s_856_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(lean_object* v_____s_878_, uint8_t v_isLower_879_, lean_object* v_as_880_, size_t v_sz_881_, size_t v_i_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = lean_usize_dec_lt(v_i_882_, v_sz_881_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_b_883_);
return v___x_897_;
}
else
{
lean_object* v_snd_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_966_; 
v_snd_898_ = lean_ctor_get(v_b_883_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_b_883_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v_b_883_, 0);
lean_dec(v_unused_967_);
v___x_900_ = v_b_883_;
v_isShared_901_ = v_isSharedCheck_966_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_snd_898_);
lean_dec(v_b_883_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_966_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_a_902_; lean_object* v_p_903_; lean_object* v___x_904_; 
v_a_902_ = lean_array_uget_borrowed(v_as_880_, v_i_882_);
v_p_903_ = lean_ctor_get(v_a_902_, 0);
v___x_904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_903_, v_____s_878_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v_a_908_; uint8_t v___y_916_; 
lean_dec_ref_known(v___x_904_, 1);
v___x_905_ = lean_box(0);
v___x_906_ = lean_box(0);
if (lean_obj_tag(v_p_903_) == 1)
{
lean_object* v_k_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_k_945_ = lean_ctor_get(v_p_903_, 0);
v___x_946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_947_ = lean_int_dec_lt(v_k_945_, v___x_946_);
if (v___x_947_ == 0)
{
if (v_isLower_879_ == 0)
{
v___y_916_ = v___x_896_;
goto v___jp_915_;
}
else
{
v___y_916_ = v___x_947_;
goto v___jp_915_;
}
}
else
{
v___y_916_ = v_isLower_879_;
goto v___jp_915_;
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_snd_898_);
v___x_948_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_949_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_948_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_dec_ref_known(v___x_949_, 1);
v_a_908_ = v___x_905_;
goto v___jp_907_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_del_object(v___x_900_);
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
v___jp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v_a_908_);
lean_ctor_set(v___x_900_, 0, v___x_906_);
v___x_910_ = v___x_900_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_a_908_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_882_, v___x_911_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_878_, v_isLower_879_, v_as_880_, v_sz_881_, v___x_912_, v___x_910_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_913_;
}
}
v___jp_915_:
{
if (v___y_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_918_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_917_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_936_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_936_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_936_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_936_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
if (lean_obj_tag(v_a_919_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_934_; 
lean_del_object(v___x_900_);
v_a_923_ = lean_ctor_get(v_a_919_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_934_ == 0)
{
v___x_925_ = v_a_919_;
v_isShared_926_ = v_isSharedCheck_934_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v_a_919_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_934_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 1);
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_933_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_snd_898_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_929_);
v___x_931_ = v___x_921_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_935_; 
lean_del_object(v___x_921_);
lean_dec(v_snd_898_);
v_a_935_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v_a_919_, 1);
v_a_908_ = v_a_935_;
goto v___jp_907_;
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_del_object(v___x_900_);
lean_dec(v_snd_898_);
v_a_937_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_918_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_918_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_dec(v_snd_898_);
v_a_908_ = v___x_905_;
goto v___jp_907_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_del_object(v___x_900_);
lean_dec(v_snd_898_);
v_a_958_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_904_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_904_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_968_ = _args[0];
lean_object* v_isLower_969_ = _args[1];
lean_object* v_as_970_ = _args[2];
lean_object* v_sz_971_ = _args[3];
lean_object* v_i_972_ = _args[4];
lean_object* v_b_973_ = _args[5];
lean_object* v___y_974_ = _args[6];
lean_object* v___y_975_ = _args[7];
lean_object* v___y_976_ = _args[8];
lean_object* v___y_977_ = _args[9];
lean_object* v___y_978_ = _args[10];
lean_object* v___y_979_ = _args[11];
lean_object* v___y_980_ = _args[12];
lean_object* v___y_981_ = _args[13];
lean_object* v___y_982_ = _args[14];
lean_object* v___y_983_ = _args[15];
lean_object* v___y_984_ = _args[16];
lean_object* v___y_985_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_986_; size_t v_sz_boxed_987_; size_t v_i_boxed_988_; lean_object* v_res_989_; 
v_isLower_boxed_986_ = lean_unbox(v_isLower_969_);
v_sz_boxed_987_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_988_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_968_, v_isLower_boxed_986_, v_as_970_, v_sz_boxed_987_, v_i_boxed_988_, v_b_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v_as_970_);
lean_dec(v_____s_968_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(lean_object* v_____s_990_, uint8_t v_isLower_991_, lean_object* v_t_992_, lean_object* v_init_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_root_1006_; lean_object* v_tail_1007_; lean_object* v___x_1008_; 
v_root_1006_ = lean_ctor_get(v_t_992_, 0);
v_tail_1007_ = lean_ctor_get(v_t_992_, 1);
v___x_1008_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_993_, v_____s_990_, v_isLower_991_, v_root_1006_, v_init_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1045_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1045_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1045_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
if (lean_obj_tag(v_a_1009_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; 
v_a_1013_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v_a_1009_, 1);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_a_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; size_t v_sz_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
lean_del_object(v___x_1011_);
v_a_1017_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v_a_1009_, 1);
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_a_1017_);
v_sz_1020_ = lean_array_size(v_tail_1007_);
v___x_1021_ = ((size_t)0ULL);
v___x_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_990_, v_isLower_991_, v_tail_1007_, v_sz_1020_, v___x_1021_, v___x_1019_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1036_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1036_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1036_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_fst_1027_; 
v_fst_1027_ = lean_ctor_get(v_a_1023_, 0);
if (lean_obj_tag(v_fst_1027_) == 0)
{
lean_object* v_snd_1028_; lean_object* v___x_1030_; 
v_snd_1028_ = lean_ctor_get(v_a_1023_, 1);
lean_inc(v_snd_1028_);
lean_dec(v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_snd_1028_);
v___x_1030_ = v___x_1025_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_snd_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
lean_object* v_val_1032_; lean_object* v___x_1034_; 
lean_inc_ref(v_fst_1027_);
lean_dec(v_a_1023_);
v_val_1032_ = lean_ctor_get(v_fst_1027_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v_fst_1027_, 1);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_val_1032_);
v___x_1034_ = v___x_1025_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_val_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1022_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1022_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_a_1046_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1008_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1008_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1054_, lean_object* v_isLower_1055_, lean_object* v_t_1056_, lean_object* v_init_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v_isLower_boxed_1070_; lean_object* v_res_1071_; 
v_isLower_boxed_1070_ = lean_unbox(v_isLower_1055_);
v_res_1071_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_____s_1054_, v_isLower_boxed_1070_, v_t_1056_, v_init_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v_t_1056_);
lean_dec(v_____s_1054_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1072_, lean_object* v_as_1073_, size_t v_sz_1074_, size_t v_i_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_usize_dec_lt(v_i_1075_, v_sz_1074_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_b_1076_);
return v___x_1090_;
}
else
{
lean_object* v_snd_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1115_; 
v_snd_1091_ = lean_ctor_get(v_b_1076_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_b_1076_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v_b_1076_, 0);
lean_dec(v_unused_1116_);
v___x_1093_ = v_b_1076_;
v_isShared_1094_ = v_isSharedCheck_1115_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_snd_1091_);
lean_dec(v_b_1076_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1115_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_a_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_a_1095_ = lean_array_uget_borrowed(v_as_1073_, v_i_1075_);
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1091_, v_isLower_1072_, v_a_1095_, v___x_1096_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
lean_dec_ref_known(v___x_1097_, 1);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_nat_add(v_snd_1091_, v___x_1099_);
lean_dec(v_snd_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1100_);
lean_ctor_set(v___x_1093_, 0, v___x_1098_);
v___x_1102_ = v___x_1093_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
size_t v___x_1103_; size_t v___x_1104_; 
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_add(v_i_1075_, v___x_1103_);
v_i_1075_ = v___x_1104_;
v_b_1076_ = v___x_1102_;
goto _start;
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1093_);
lean_dec(v_snd_1091_);
v_a_1107_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1097_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1097_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object** _args){
lean_object* v_isLower_1117_ = _args[0];
lean_object* v_as_1118_ = _args[1];
lean_object* v_sz_1119_ = _args[2];
lean_object* v_i_1120_ = _args[3];
lean_object* v_b_1121_ = _args[4];
lean_object* v___y_1122_ = _args[5];
lean_object* v___y_1123_ = _args[6];
lean_object* v___y_1124_ = _args[7];
lean_object* v___y_1125_ = _args[8];
lean_object* v___y_1126_ = _args[9];
lean_object* v___y_1127_ = _args[10];
lean_object* v___y_1128_ = _args[11];
lean_object* v___y_1129_ = _args[12];
lean_object* v___y_1130_ = _args[13];
lean_object* v___y_1131_ = _args[14];
lean_object* v___y_1132_ = _args[15];
lean_object* v___y_1133_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1134_; size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_isLower_boxed_1134_ = lean_unbox(v_isLower_1117_);
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1134_, v_as_1118_, v_sz_boxed_1135_, v_i_boxed_1136_, v_b_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v_as_1118_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1138_, lean_object* v_as_1139_, size_t v_sz_1140_, size_t v_i_1141_, lean_object* v_b_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_lt(v_i_1141_, v_sz_1140_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_b_1142_);
return v___x_1156_;
}
else
{
lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1181_; 
v_snd_1157_ = lean_ctor_get(v_b_1142_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_b_1142_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v_b_1142_, 0);
lean_dec(v_unused_1182_);
v___x_1159_ = v_b_1142_;
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_dec(v_b_1142_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_a_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_a_1161_ = lean_array_uget_borrowed(v_as_1139_, v_i_1141_);
v___x_1162_ = lean_box(0);
v___x_1163_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1157_, v_isLower_1138_, v_a_1161_, v___x_1162_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_dec_ref_known(v___x_1163_, 1);
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_add(v_snd_1157_, v___x_1165_);
lean_dec(v_snd_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1166_);
lean_ctor_set(v___x_1159_, 0, v___x_1164_);
v___x_1168_ = v___x_1159_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
size_t v___x_1169_; size_t v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_add(v_i_1141_, v___x_1169_);
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1138_, v_as_1139_, v_sz_1140_, v___x_1170_, v___x_1168_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1171_;
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_del_object(v___x_1159_);
lean_dec(v_snd_1157_);
v_a_1173_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1163_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1163_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object** _args){
lean_object* v_isLower_1183_ = _args[0];
lean_object* v_as_1184_ = _args[1];
lean_object* v_sz_1185_ = _args[2];
lean_object* v_i_1186_ = _args[3];
lean_object* v_b_1187_ = _args[4];
lean_object* v___y_1188_ = _args[5];
lean_object* v___y_1189_ = _args[6];
lean_object* v___y_1190_ = _args[7];
lean_object* v___y_1191_ = _args[8];
lean_object* v___y_1192_ = _args[9];
lean_object* v___y_1193_ = _args[10];
lean_object* v___y_1194_ = _args[11];
lean_object* v___y_1195_ = _args[12];
lean_object* v___y_1196_ = _args[13];
lean_object* v___y_1197_ = _args[14];
lean_object* v___y_1198_ = _args[15];
lean_object* v___y_1199_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1200_; size_t v_sz_boxed_1201_; size_t v_i_boxed_1202_; lean_object* v_res_1203_; 
v_isLower_boxed_1200_ = lean_unbox(v_isLower_1183_);
v_sz_boxed_1201_ = lean_unbox_usize(v_sz_1185_);
lean_dec(v_sz_1185_);
v_i_boxed_1202_ = lean_unbox_usize(v_i_1186_);
lean_dec(v_i_1186_);
v_res_1203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1200_, v_as_1184_, v_sz_boxed_1201_, v_i_boxed_1202_, v_b_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v_as_1184_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(lean_object* v_init_1204_, uint8_t v_isLower_1205_, lean_object* v_n_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
if (lean_obj_tag(v_n_1206_) == 0)
{
lean_object* v_cs_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; size_t v_sz_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v_cs_1220_ = lean_ctor_get(v_n_1206_, 0);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_b_1207_);
v_sz_1223_ = lean_array_size(v_cs_1220_);
v___x_1224_ = ((size_t)0ULL);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1204_, v_isLower_1205_, v_cs_1220_, v_sz_1223_, v___x_1224_, v___x_1222_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1240_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1240_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1240_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_fst_1230_; 
v_fst_1230_ = lean_ctor_get(v_a_1226_, 0);
if (lean_obj_tag(v_fst_1230_) == 0)
{
lean_object* v_snd_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v_snd_1231_ = lean_ctor_get(v_a_1226_, 1);
lean_inc(v_snd_1231_);
lean_dec(v_a_1226_);
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_snd_1231_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1232_);
v___x_1234_ = v___x_1228_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
else
{
lean_object* v_val_1236_; lean_object* v___x_1238_; 
lean_inc_ref(v_fst_1230_);
lean_dec(v_a_1226_);
v_val_1236_ = lean_ctor_get(v_fst_1230_, 0);
lean_inc(v_val_1236_);
lean_dec_ref_known(v_fst_1230_, 1);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v_val_1236_);
v___x_1238_ = v___x_1228_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_val_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1225_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1225_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_vs_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v_vs_1249_ = lean_ctor_get(v_n_1206_, 0);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_b_1207_);
v_sz_1252_ = lean_array_size(v_vs_1249_);
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1205_, v_vs_1249_, v_sz_1252_, v___x_1253_, v___x_1251_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1269_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1269_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1269_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_fst_1259_; 
v_fst_1259_ = lean_ctor_get(v_a_1255_, 0);
if (lean_obj_tag(v_fst_1259_) == 0)
{
lean_object* v_snd_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v_snd_1260_ = lean_ctor_get(v_a_1255_, 1);
lean_inc(v_snd_1260_);
lean_dec(v_a_1255_);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_snd_1260_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1261_);
v___x_1263_ = v___x_1257_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
else
{
lean_object* v_val_1265_; lean_object* v___x_1267_; 
lean_inc_ref(v_fst_1259_);
lean_dec(v_a_1255_);
v_val_1265_ = lean_ctor_get(v_fst_1259_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v_fst_1259_, 1);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_val_1265_);
v___x_1267_ = v___x_1257_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_val_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1270_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1254_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1254_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object* v_init_1278_, uint8_t v_isLower_1279_, lean_object* v_as_1280_, size_t v_sz_1281_, size_t v_i_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_usize_dec_lt(v_i_1282_, v_sz_1281_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_b_1283_);
return v___x_1297_;
}
else
{
lean_object* v_snd_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1332_; 
v_snd_1298_ = lean_ctor_get(v_b_1283_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_b_1283_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v_b_1283_, 0);
lean_dec(v_unused_1333_);
v___x_1300_ = v_b_1283_;
v_isShared_1301_ = v_isSharedCheck_1332_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_snd_1298_);
lean_dec(v_b_1283_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1332_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_a_1302_; lean_object* v___x_1303_; 
v_a_1302_ = lean_array_uget_borrowed(v_as_1280_, v_i_1282_);
lean_inc(v_snd_1298_);
v___x_1303_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_1278_, v_isLower_1279_, v_a_1302_, v_snd_1298_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1323_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1323_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1323_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
if (lean_obj_tag(v_a_1304_) == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_a_1304_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1308_);
v___x_1310_ = v___x_1300_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_snd_1298_);
v___x_1310_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1310_);
v___x_1312_ = v___x_1306_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_del_object(v___x_1306_);
lean_dec(v_snd_1298_);
v_a_1315_ = lean_ctor_get(v_a_1304_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v_a_1304_, 1);
v___x_1316_ = lean_box(0);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v_a_1315_);
lean_ctor_set(v___x_1300_, 0, v___x_1316_);
v___x_1318_ = v___x_1300_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_a_1315_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
size_t v___x_1319_; size_t v___x_1320_; 
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_add(v_i_1282_, v___x_1319_);
v_i_1282_ = v___x_1320_;
v_b_1283_ = v___x_1318_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_del_object(v___x_1300_);
lean_dec(v_snd_1298_);
v_a_1324_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1303_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1303_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_init_1334_ = _args[0];
lean_object* v_isLower_1335_ = _args[1];
lean_object* v_as_1336_ = _args[2];
lean_object* v_sz_1337_ = _args[3];
lean_object* v_i_1338_ = _args[4];
lean_object* v_b_1339_ = _args[5];
lean_object* v___y_1340_ = _args[6];
lean_object* v___y_1341_ = _args[7];
lean_object* v___y_1342_ = _args[8];
lean_object* v___y_1343_ = _args[9];
lean_object* v___y_1344_ = _args[10];
lean_object* v___y_1345_ = _args[11];
lean_object* v___y_1346_ = _args[12];
lean_object* v___y_1347_ = _args[13];
lean_object* v___y_1348_ = _args[14];
lean_object* v___y_1349_ = _args[15];
lean_object* v___y_1350_ = _args[16];
lean_object* v___y_1351_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_1352_; size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v_isLower_boxed_1352_ = lean_unbox(v_isLower_1335_);
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1334_, v_isLower_boxed_1352_, v_as_1336_, v_sz_boxed_1353_, v_i_boxed_1354_, v_b_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v_as_1336_);
lean_dec(v_init_1334_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_init_1356_, lean_object* v_isLower_1357_, lean_object* v_n_1358_, lean_object* v_b_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v_isLower_boxed_1372_; lean_object* v_res_1373_; 
v_isLower_boxed_1372_ = lean_unbox(v_isLower_1357_);
v_res_1373_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_1356_, v_isLower_boxed_1372_, v_n_1358_, v_b_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v_n_1358_);
lean_dec(v_init_1356_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1374_, lean_object* v_as_1375_, size_t v_sz_1376_, size_t v_i_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_usize_dec_lt(v_i_1377_, v_sz_1376_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_b_1378_);
return v___x_1392_;
}
else
{
lean_object* v_snd_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1417_; 
v_snd_1393_ = lean_ctor_get(v_b_1378_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_b_1378_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_b_1378_, 0);
lean_dec(v_unused_1418_);
v___x_1395_ = v_b_1378_;
v_isShared_1396_ = v_isSharedCheck_1417_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_snd_1393_);
lean_dec(v_b_1378_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1417_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_a_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_a_1397_ = lean_array_uget_borrowed(v_as_1375_, v_i_1377_);
v___x_1398_ = lean_box(0);
v___x_1399_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1393_, v_isLower_1374_, v_a_1397_, v___x_1398_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec_ref_known(v___x_1399_, 1);
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_add(v_snd_1393_, v___x_1401_);
lean_dec(v_snd_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___x_1402_);
lean_ctor_set(v___x_1395_, 0, v___x_1400_);
v___x_1404_ = v___x_1395_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
size_t v___x_1405_; size_t v___x_1406_; 
v___x_1405_ = ((size_t)1ULL);
v___x_1406_ = lean_usize_add(v_i_1377_, v___x_1405_);
v_i_1377_ = v___x_1406_;
v_b_1378_ = v___x_1404_;
goto _start;
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_del_object(v___x_1395_);
lean_dec(v_snd_1393_);
v_a_1409_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1399_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1399_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object** _args){
lean_object* v_isLower_1419_ = _args[0];
lean_object* v_as_1420_ = _args[1];
lean_object* v_sz_1421_ = _args[2];
lean_object* v_i_1422_ = _args[3];
lean_object* v_b_1423_ = _args[4];
lean_object* v___y_1424_ = _args[5];
lean_object* v___y_1425_ = _args[6];
lean_object* v___y_1426_ = _args[7];
lean_object* v___y_1427_ = _args[8];
lean_object* v___y_1428_ = _args[9];
lean_object* v___y_1429_ = _args[10];
lean_object* v___y_1430_ = _args[11];
lean_object* v___y_1431_ = _args[12];
lean_object* v___y_1432_ = _args[13];
lean_object* v___y_1433_ = _args[14];
lean_object* v___y_1434_ = _args[15];
lean_object* v___y_1435_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1436_; size_t v_sz_boxed_1437_; size_t v_i_boxed_1438_; lean_object* v_res_1439_; 
v_isLower_boxed_1436_ = lean_unbox(v_isLower_1419_);
v_sz_boxed_1437_ = lean_unbox_usize(v_sz_1421_);
lean_dec(v_sz_1421_);
v_i_boxed_1438_ = lean_unbox_usize(v_i_1422_);
lean_dec(v_i_1422_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_1436_, v_as_1420_, v_sz_boxed_1437_, v_i_boxed_1438_, v_b_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v_as_1420_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1440_, lean_object* v_as_1441_, size_t v_sz_1442_, size_t v_i_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_usize_dec_lt(v_i_1443_, v_sz_1442_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v_b_1444_);
return v___x_1458_;
}
else
{
lean_object* v_snd_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1483_; 
v_snd_1459_ = lean_ctor_get(v_b_1444_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_b_1444_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; 
v_unused_1484_ = lean_ctor_get(v_b_1444_, 0);
lean_dec(v_unused_1484_);
v___x_1461_ = v_b_1444_;
v_isShared_1462_ = v_isSharedCheck_1483_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_snd_1459_);
lean_dec(v_b_1444_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1483_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_a_1463_ = lean_array_uget_borrowed(v_as_1441_, v_i_1443_);
v___x_1464_ = lean_box(0);
v___x_1465_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1459_, v_isLower_1440_, v_a_1463_, v___x_1464_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec_ref_known(v___x_1465_, 1);
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_snd_1459_, v___x_1467_);
lean_dec(v_snd_1459_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v___x_1468_);
lean_ctor_set(v___x_1461_, 0, v___x_1466_);
v___x_1470_ = v___x_1461_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
size_t v___x_1471_; size_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = lean_usize_add(v_i_1443_, v___x_1471_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1440_, v_as_1441_, v_sz_1442_, v___x_1472_, v___x_1470_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1473_;
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_del_object(v___x_1461_);
lean_dec(v_snd_1459_);
v_a_1475_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1465_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1465_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_isLower_1485_ = _args[0];
lean_object* v_as_1486_ = _args[1];
lean_object* v_sz_1487_ = _args[2];
lean_object* v_i_1488_ = _args[3];
lean_object* v_b_1489_ = _args[4];
lean_object* v___y_1490_ = _args[5];
lean_object* v___y_1491_ = _args[6];
lean_object* v___y_1492_ = _args[7];
lean_object* v___y_1493_ = _args[8];
lean_object* v___y_1494_ = _args[9];
lean_object* v___y_1495_ = _args[10];
lean_object* v___y_1496_ = _args[11];
lean_object* v___y_1497_ = _args[12];
lean_object* v___y_1498_ = _args[13];
lean_object* v___y_1499_ = _args[14];
lean_object* v___y_1500_ = _args[15];
lean_object* v___y_1501_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1502_; size_t v_sz_boxed_1503_; size_t v_i_boxed_1504_; lean_object* v_res_1505_; 
v_isLower_boxed_1502_ = lean_unbox(v_isLower_1485_);
v_sz_boxed_1503_ = lean_unbox_usize(v_sz_1487_);
lean_dec(v_sz_1487_);
v_i_boxed_1504_ = lean_unbox_usize(v_i_1488_);
lean_dec(v_i_1488_);
v_res_1505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1502_, v_as_1486_, v_sz_boxed_1503_, v_i_boxed_1504_, v_b_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v_as_1486_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(uint8_t v_isLower_1506_, lean_object* v_t_1507_, lean_object* v_init_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_root_1521_; lean_object* v_tail_1522_; lean_object* v___x_1523_; 
v_root_1521_ = lean_ctor_get(v_t_1507_, 0);
v_tail_1522_ = lean_ctor_get(v_t_1507_, 1);
lean_inc(v_init_1508_);
v___x_1523_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_1508_, v_isLower_1506_, v_root_1521_, v_init_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v_init_1508_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1560_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1560_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1560_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
if (lean_obj_tag(v_a_1524_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1530_; 
v_a_1528_ = lean_ctor_get(v_a_1524_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v_a_1524_, 1);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_a_1528_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; size_t v_sz_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
lean_del_object(v___x_1526_);
v_a_1532_ = lean_ctor_get(v_a_1524_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v_a_1524_, 1);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v_a_1532_);
v_sz_1535_ = lean_array_size(v_tail_1522_);
v___x_1536_ = ((size_t)0ULL);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_1506_, v_tail_1522_, v_sz_1535_, v___x_1536_, v___x_1534_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1551_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1551_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1551_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_fst_1542_; 
v_fst_1542_ = lean_ctor_get(v_a_1538_, 0);
if (lean_obj_tag(v_fst_1542_) == 0)
{
lean_object* v_snd_1543_; lean_object* v___x_1545_; 
v_snd_1543_ = lean_ctor_get(v_a_1538_, 1);
lean_inc(v_snd_1543_);
lean_dec(v_a_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_snd_1543_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_snd_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
else
{
lean_object* v_val_1547_; lean_object* v___x_1549_; 
lean_inc_ref(v_fst_1542_);
lean_dec(v_a_1538_);
v_val_1547_ = lean_ctor_get(v_fst_1542_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_fst_1542_, 1);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_val_1547_);
v___x_1549_ = v___x_1540_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_val_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1537_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1537_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1523_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1523_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1569_, lean_object* v_t_1570_, lean_object* v_init_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
uint8_t v_isLower_boxed_1584_; lean_object* v_res_1585_; 
v_isLower_boxed_1584_ = lean_unbox(v_isLower_1569_);
v_res_1585_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_boxed_1584_, v_t_1570_, v_init_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v_t_1570_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(lean_object* v_css_1586_, uint8_t v_isLower_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_x_1600_; lean_object* v___x_1601_; 
v_x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_1587_, v_css_1586_, v_x_1600_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1609_; 
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v___x_1601_, 0);
lean_dec(v_unused_1610_);
v___x_1603_ = v___x_1601_;
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v___x_1601_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_box(0);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1601_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1601_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs___boxed(lean_object* v_css_1619_, lean_object* v_isLower_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
uint8_t v_isLower_boxed_1633_; lean_object* v_res_1634_; 
v_isLower_boxed_1633_ = lean_unbox(v_isLower_1620_);
v_res_1634_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_css_1619_, v_isLower_boxed_1633_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_css_1619_);
return v_res_1634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1));
v___x_1638_ = lean_unsigned_to_nat(2u);
v___x_1639_ = lean_unsigned_to_nat(63u);
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0));
v___x_1641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_1642_ = l_mkPanicMessageWithDecl(v___x_1641_, v___x_1640_, v___x_1639_, v___x_1638_, v___x_1637_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v_lowers_1657_; lean_object* v_vars_1658_; lean_object* v_size_1659_; lean_object* v_size_1660_; uint8_t v___x_1661_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v_lowers_1657_ = lean_ctor_get(v_a_1656_, 32);
lean_inc_ref(v_lowers_1657_);
v_vars_1658_ = lean_ctor_get(v_a_1656_, 30);
lean_inc_ref(v_vars_1658_);
lean_dec(v_a_1656_);
v_size_1659_ = lean_ctor_get(v_lowers_1657_, 2);
v_size_1660_ = lean_ctor_get(v_vars_1658_, 2);
lean_inc(v_size_1660_);
lean_dec_ref(v_vars_1658_);
v___x_1661_ = lean_nat_dec_eq(v_size_1659_, v_size_1660_);
lean_dec(v_size_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v_lowers_1657_);
v___x_1662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2);
v___x_1663_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_1662_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_lowers_1657_, v___x_1661_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_lowers_1657_);
return v___x_1664_;
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1655_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1655_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___boxed(lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec(v_a_1673_);
return v_res_1685_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1));
v___x_1689_ = lean_unsigned_to_nat(2u);
v___x_1690_ = lean_unsigned_to_nat(68u);
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0));
v___x_1692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_1693_ = l_mkPanicMessageWithDecl(v___x_1692_, v___x_1691_, v___x_1690_, v___x_1689_, v___x_1688_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v_uppers_1708_; lean_object* v_vars_1709_; lean_object* v_size_1710_; lean_object* v_size_1711_; uint8_t v___x_1712_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v_uppers_1708_ = lean_ctor_get(v_a_1707_, 33);
lean_inc_ref(v_uppers_1708_);
v_vars_1709_ = lean_ctor_get(v_a_1707_, 30);
lean_inc_ref(v_vars_1709_);
lean_dec(v_a_1707_);
v_size_1710_ = lean_ctor_get(v_uppers_1708_, 2);
v_size_1711_ = lean_ctor_get(v_vars_1709_, 2);
lean_inc(v_size_1711_);
lean_dec_ref(v_vars_1709_);
v___x_1712_ = lean_nat_dec_eq(v_size_1710_, v_size_1711_);
lean_dec(v_size_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref(v_uppers_1708_);
v___x_1713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2);
v___x_1714_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_1713_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1714_;
}
else
{
uint8_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = 0;
v___x_1716_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_uppers_1708_, v___x_1715_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec_ref(v_uppers_1708_);
return v___x_1716_;
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_a_1717_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1706_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1706_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___boxed(lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec(v_a_1725_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_1741_, lean_object* v_as_1742_, size_t v_sz_1743_, size_t v_i_1744_, lean_object* v_b_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_lt(v_i_1744_, v_sz_1743_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_b_1745_);
return v___x_1759_;
}
else
{
lean_object* v_a_1760_; lean_object* v_p_1761_; lean_object* v___x_1762_; 
lean_dec_ref(v_b_1745_);
v_a_1760_ = lean_array_uget_borrowed(v_as_1742_, v_i_1744_);
v_p_1761_ = lean_ctor_get(v_a_1760_, 0);
v___x_1762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_1761_, v_____s_1741_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v___x_1763_; size_t v___x_1764_; size_t v___x_1765_; 
lean_dec_ref_known(v___x_1762_, 1);
v___x_1763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1744_, v___x_1764_);
v_i_1744_ = v___x_1765_;
v_b_1745_ = v___x_1763_;
goto _start;
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1762_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1762_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_____s_1775_ = _args[0];
lean_object* v_as_1776_ = _args[1];
lean_object* v_sz_1777_ = _args[2];
lean_object* v_i_1778_ = _args[3];
lean_object* v_b_1779_ = _args[4];
lean_object* v___y_1780_ = _args[5];
lean_object* v___y_1781_ = _args[6];
lean_object* v___y_1782_ = _args[7];
lean_object* v___y_1783_ = _args[8];
lean_object* v___y_1784_ = _args[9];
lean_object* v___y_1785_ = _args[10];
lean_object* v___y_1786_ = _args[11];
lean_object* v___y_1787_ = _args[12];
lean_object* v___y_1788_ = _args[13];
lean_object* v___y_1789_ = _args[14];
lean_object* v___y_1790_ = _args[15];
lean_object* v___y_1791_ = _args[16];
_start:
{
size_t v_sz_boxed_1792_; size_t v_i_boxed_1793_; lean_object* v_res_1794_; 
v_sz_boxed_1792_ = lean_unbox_usize(v_sz_1777_);
lean_dec(v_sz_1777_);
v_i_boxed_1793_ = lean_unbox_usize(v_i_1778_);
lean_dec(v_i_1778_);
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_1775_, v_as_1776_, v_sz_boxed_1792_, v_i_boxed_1793_, v_b_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v_as_1776_);
lean_dec(v_____s_1775_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_1795_, lean_object* v_as_1796_, size_t v_sz_1797_, size_t v_i_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_usize_dec_lt(v_i_1798_, v_sz_1797_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_b_1799_);
return v___x_1813_;
}
else
{
lean_object* v_a_1814_; lean_object* v_p_1815_; lean_object* v___x_1816_; 
lean_dec_ref(v_b_1799_);
v_a_1814_ = lean_array_uget_borrowed(v_as_1796_, v_i_1798_);
v_p_1815_ = lean_ctor_get(v_a_1814_, 0);
v___x_1816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_1815_, v_____s_1795_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; size_t v___x_1818_; size_t v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref_known(v___x_1816_, 1);
v___x_1817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_1818_ = ((size_t)1ULL);
v___x_1819_ = lean_usize_add(v_i_1798_, v___x_1818_);
v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_1795_, v_as_1796_, v_sz_1797_, v___x_1819_, v___x_1817_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1820_;
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1816_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1816_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_____s_1829_ = _args[0];
lean_object* v_as_1830_ = _args[1];
lean_object* v_sz_1831_ = _args[2];
lean_object* v_i_1832_ = _args[3];
lean_object* v_b_1833_ = _args[4];
lean_object* v___y_1834_ = _args[5];
lean_object* v___y_1835_ = _args[6];
lean_object* v___y_1836_ = _args[7];
lean_object* v___y_1837_ = _args[8];
lean_object* v___y_1838_ = _args[9];
lean_object* v___y_1839_ = _args[10];
lean_object* v___y_1840_ = _args[11];
lean_object* v___y_1841_ = _args[12];
lean_object* v___y_1842_ = _args[13];
lean_object* v___y_1843_ = _args[14];
lean_object* v___y_1844_ = _args[15];
lean_object* v___y_1845_ = _args[16];
_start:
{
size_t v_sz_boxed_1846_; size_t v_i_boxed_1847_; lean_object* v_res_1848_; 
v_sz_boxed_1846_ = lean_unbox_usize(v_sz_1831_);
lean_dec(v_sz_1831_);
v_i_boxed_1847_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_res_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_1829_, v_as_1830_, v_sz_boxed_1846_, v_i_boxed_1847_, v_b_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v_as_1830_);
lean_dec(v_____s_1829_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_init_1849_, lean_object* v_____s_1850_, lean_object* v_n_1851_, lean_object* v_b_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
if (lean_obj_tag(v_n_1851_) == 0)
{
lean_object* v_cs_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; size_t v_sz_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v_cs_1865_ = lean_ctor_get(v_n_1851_, 0);
v___x_1866_ = lean_box(0);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v_b_1852_);
v_sz_1868_ = lean_array_size(v_cs_1865_);
v___x_1869_ = ((size_t)0ULL);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_1849_, v_____s_1850_, v_cs_1865_, v_sz_1868_, v___x_1869_, v___x_1867_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1885_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1885_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1885_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_fst_1875_; 
v_fst_1875_ = lean_ctor_get(v_a_1871_, 0);
if (lean_obj_tag(v_fst_1875_) == 0)
{
lean_object* v_snd_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v_snd_1876_ = lean_ctor_get(v_a_1871_, 1);
lean_inc(v_snd_1876_);
lean_dec(v_a_1871_);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_snd_1876_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1877_);
v___x_1879_ = v___x_1873_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v_val_1881_; lean_object* v___x_1883_; 
lean_inc_ref(v_fst_1875_);
lean_dec(v_a_1871_);
v_val_1881_ = lean_ctor_get(v_fst_1875_, 0);
lean_inc(v_val_1881_);
lean_dec_ref_known(v_fst_1875_, 1);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_val_1881_);
v___x_1883_ = v___x_1873_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_val_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_a_1886_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1870_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1870_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_vs_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; size_t v_sz_1897_; size_t v___x_1898_; lean_object* v___x_1899_; 
v_vs_1894_ = lean_ctor_get(v_n_1851_, 0);
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v_b_1852_);
v_sz_1897_ = lean_array_size(v_vs_1894_);
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_1850_, v_vs_1894_, v_sz_1897_, v___x_1898_, v___x_1896_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1914_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1914_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1914_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_fst_1904_; 
v_fst_1904_ = lean_ctor_get(v_a_1900_, 0);
if (lean_obj_tag(v_fst_1904_) == 0)
{
lean_object* v_snd_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v_snd_1905_ = lean_ctor_get(v_a_1900_, 1);
lean_inc(v_snd_1905_);
lean_dec(v_a_1900_);
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_snd_1905_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1906_);
v___x_1908_ = v___x_1902_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
else
{
lean_object* v_val_1910_; lean_object* v___x_1912_; 
lean_inc_ref(v_fst_1904_);
lean_dec(v_a_1900_);
v_val_1910_ = lean_ctor_get(v_fst_1904_, 0);
lean_inc(v_val_1910_);
lean_dec_ref_known(v_fst_1904_, 1);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_val_1910_);
v___x_1912_ = v___x_1902_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_val_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1899_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1899_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_1923_, lean_object* v_____s_1924_, lean_object* v_as_1925_, size_t v_sz_1926_, size_t v_i_1927_, lean_object* v_b_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1927_, v_sz_1926_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_b_1928_);
return v___x_1942_;
}
else
{
lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1977_; 
v_snd_1943_ = lean_ctor_get(v_b_1928_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_b_1928_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v_b_1928_, 0);
lean_dec(v_unused_1978_);
v___x_1945_ = v_b_1928_;
v_isShared_1946_ = v_isSharedCheck_1977_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_dec(v_b_1928_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1977_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_a_1947_; lean_object* v___x_1948_; 
v_a_1947_ = lean_array_uget_borrowed(v_as_1925_, v_i_1927_);
lean_inc(v_snd_1943_);
v___x_1948_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_1923_, v_____s_1924_, v_a_1947_, v_snd_1943_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1968_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1968_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1968_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
if (lean_obj_tag(v_a_1949_) == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1949_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1953_);
v___x_1955_ = v___x_1945_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_snd_1943_);
v___x_1955_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1955_);
v___x_1957_ = v___x_1951_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_del_object(v___x_1951_);
lean_dec(v_snd_1943_);
v_a_1960_ = lean_ctor_get(v_a_1949_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v_a_1949_, 1);
v___x_1961_ = lean_box(0);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v_a_1960_);
lean_ctor_set(v___x_1945_, 0, v___x_1961_);
v___x_1963_ = v___x_1945_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_a_1960_);
v___x_1963_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
size_t v___x_1964_; size_t v___x_1965_; 
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_i_1927_, v___x_1964_);
v_i_1927_ = v___x_1965_;
v_b_1928_ = v___x_1963_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_del_object(v___x_1945_);
lean_dec(v_snd_1943_);
v_a_1969_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1948_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1948_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1979_ = _args[0];
lean_object* v_____s_1980_ = _args[1];
lean_object* v_as_1981_ = _args[2];
lean_object* v_sz_1982_ = _args[3];
lean_object* v_i_1983_ = _args[4];
lean_object* v_b_1984_ = _args[5];
lean_object* v___y_1985_ = _args[6];
lean_object* v___y_1986_ = _args[7];
lean_object* v___y_1987_ = _args[8];
lean_object* v___y_1988_ = _args[9];
lean_object* v___y_1989_ = _args[10];
lean_object* v___y_1990_ = _args[11];
lean_object* v___y_1991_ = _args[12];
lean_object* v___y_1992_ = _args[13];
lean_object* v___y_1993_ = _args[14];
lean_object* v___y_1994_ = _args[15];
lean_object* v___y_1995_ = _args[16];
lean_object* v___y_1996_ = _args[17];
_start:
{
size_t v_sz_boxed_1997_; size_t v_i_boxed_1998_; lean_object* v_res_1999_; 
v_sz_boxed_1997_ = lean_unbox_usize(v_sz_1982_);
lean_dec(v_sz_1982_);
v_i_boxed_1998_ = lean_unbox_usize(v_i_1983_);
lean_dec(v_i_1983_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_1979_, v_____s_1980_, v_as_1981_, v_sz_boxed_1997_, v_i_boxed_1998_, v_b_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v_as_1981_);
lean_dec(v_____s_1980_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_init_2000_, lean_object* v_____s_2001_, lean_object* v_n_2002_, lean_object* v_b_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_2000_, v_____s_2001_, v_n_2002_, v_b_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v_n_2002_);
lean_dec(v_____s_2001_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_2020_, lean_object* v_as_2021_, size_t v_sz_2022_, size_t v_i_2023_, lean_object* v_b_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_usize_dec_lt(v_i_2023_, v_sz_2022_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v_b_2024_);
return v___x_2038_;
}
else
{
lean_object* v_a_2039_; lean_object* v_p_2040_; lean_object* v___x_2041_; 
lean_dec_ref(v_b_2024_);
v_a_2039_ = lean_array_uget_borrowed(v_as_2021_, v_i_2023_);
v_p_2040_ = lean_ctor_get(v_a_2039_, 0);
v___x_2041_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_2040_, v_____s_2020_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; 
lean_dec_ref_known(v___x_2041_, 1);
v___x_2042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_2043_ = ((size_t)1ULL);
v___x_2044_ = lean_usize_add(v_i_2023_, v___x_2043_);
v_i_2023_ = v___x_2044_;
v_b_2024_ = v___x_2042_;
goto _start;
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
v_a_2046_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2041_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2041_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_____s_2054_ = _args[0];
lean_object* v_as_2055_ = _args[1];
lean_object* v_sz_2056_ = _args[2];
lean_object* v_i_2057_ = _args[3];
lean_object* v_b_2058_ = _args[4];
lean_object* v___y_2059_ = _args[5];
lean_object* v___y_2060_ = _args[6];
lean_object* v___y_2061_ = _args[7];
lean_object* v___y_2062_ = _args[8];
lean_object* v___y_2063_ = _args[9];
lean_object* v___y_2064_ = _args[10];
lean_object* v___y_2065_ = _args[11];
lean_object* v___y_2066_ = _args[12];
lean_object* v___y_2067_ = _args[13];
lean_object* v___y_2068_ = _args[14];
lean_object* v___y_2069_ = _args[15];
lean_object* v___y_2070_ = _args[16];
_start:
{
size_t v_sz_boxed_2071_; size_t v_i_boxed_2072_; lean_object* v_res_2073_; 
v_sz_boxed_2071_ = lean_unbox_usize(v_sz_2056_);
lean_dec(v_sz_2056_);
v_i_boxed_2072_ = lean_unbox_usize(v_i_2057_);
lean_dec(v_i_2057_);
v_res_2073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_2054_, v_as_2055_, v_sz_boxed_2071_, v_i_boxed_2072_, v_b_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v_as_2055_);
lean_dec(v_____s_2054_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_2074_, lean_object* v_as_2075_, size_t v_sz_2076_, size_t v_i_2077_, lean_object* v_b_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_2091_; 
v___x_2091_ = lean_usize_dec_lt(v_i_2077_, v_sz_2076_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_b_2078_);
return v___x_2092_;
}
else
{
lean_object* v_a_2093_; lean_object* v_p_2094_; lean_object* v___x_2095_; 
lean_dec_ref(v_b_2078_);
v_a_2093_ = lean_array_uget_borrowed(v_as_2075_, v_i_2077_);
v_p_2094_ = lean_ctor_get(v_a_2093_, 0);
v___x_2095_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_2094_, v_____s_2074_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v___x_2096_; size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
lean_dec_ref_known(v___x_2095_, 1);
v___x_2096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_i_2077_, v___x_2097_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_2074_, v_as_2075_, v_sz_2076_, v___x_2098_, v___x_2096_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2099_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
v_a_2100_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2095_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2095_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_____s_2108_ = _args[0];
lean_object* v_as_2109_ = _args[1];
lean_object* v_sz_2110_ = _args[2];
lean_object* v_i_2111_ = _args[3];
lean_object* v_b_2112_ = _args[4];
lean_object* v___y_2113_ = _args[5];
lean_object* v___y_2114_ = _args[6];
lean_object* v___y_2115_ = _args[7];
lean_object* v___y_2116_ = _args[8];
lean_object* v___y_2117_ = _args[9];
lean_object* v___y_2118_ = _args[10];
lean_object* v___y_2119_ = _args[11];
lean_object* v___y_2120_ = _args[12];
lean_object* v___y_2121_ = _args[13];
lean_object* v___y_2122_ = _args[14];
lean_object* v___y_2123_ = _args[15];
lean_object* v___y_2124_ = _args[16];
_start:
{
size_t v_sz_boxed_2125_; size_t v_i_boxed_2126_; lean_object* v_res_2127_; 
v_sz_boxed_2125_ = lean_unbox_usize(v_sz_2110_);
lean_dec(v_sz_2110_);
v_i_boxed_2126_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_res_2127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_2108_, v_as_2109_, v_sz_boxed_2125_, v_i_boxed_2126_, v_b_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v_as_2109_);
lean_dec(v_____s_2108_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(lean_object* v_____s_2128_, lean_object* v_t_2129_, lean_object* v_init_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_root_2143_; lean_object* v_tail_2144_; lean_object* v___x_2145_; 
v_root_2143_ = lean_ctor_get(v_t_2129_, 0);
v_tail_2144_ = lean_ctor_get(v_t_2129_, 1);
v___x_2145_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_2130_, v_____s_2128_, v_root_2143_, v_init_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2182_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2182_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2182_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
if (lean_obj_tag(v_a_2146_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; 
v_a_2150_ = lean_ctor_get(v_a_2146_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v_a_2146_, 1);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v_a_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; size_t v_sz_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
lean_del_object(v___x_2148_);
v_a_2154_ = lean_ctor_get(v_a_2146_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v_a_2146_, 1);
v___x_2155_ = lean_box(0);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v_a_2154_);
v_sz_2157_ = lean_array_size(v_tail_2144_);
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_2128_, v_tail_2144_, v_sz_2157_, v___x_2158_, v___x_2156_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2173_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2173_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2173_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_fst_2164_; 
v_fst_2164_ = lean_ctor_get(v_a_2160_, 0);
if (lean_obj_tag(v_fst_2164_) == 0)
{
lean_object* v_snd_2165_; lean_object* v___x_2167_; 
v_snd_2165_ = lean_ctor_get(v_a_2160_, 1);
lean_inc(v_snd_2165_);
lean_dec(v_a_2160_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v_snd_2165_);
v___x_2167_ = v___x_2162_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_snd_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
else
{
lean_object* v_val_2169_; lean_object* v___x_2171_; 
lean_inc_ref(v_fst_2164_);
lean_dec(v_a_2160_);
v_val_2169_ = lean_ctor_get(v_fst_2164_, 0);
lean_inc(v_val_2169_);
lean_dec_ref_known(v_fst_2164_, 1);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v_val_2169_);
v___x_2171_ = v___x_2162_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_val_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_a_2174_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2159_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2159_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
v_a_2183_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2145_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2145_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_2191_, lean_object* v_t_2192_, lean_object* v_init_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_____s_2191_, v_t_2192_, v_init_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v_t_2192_);
lean_dec(v_____s_2191_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_2207_, size_t v_sz_2208_, size_t v_i_2209_, lean_object* v_b_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_usize_dec_lt(v_i_2209_, v_sz_2208_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_b_2210_);
return v___x_2224_;
}
else
{
lean_object* v_snd_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2249_; 
v_snd_2225_ = lean_ctor_get(v_b_2210_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_b_2210_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v_b_2210_, 0);
lean_dec(v_unused_2250_);
v___x_2227_ = v_b_2210_;
v_isShared_2228_ = v_isSharedCheck_2249_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_snd_2225_);
lean_dec(v_b_2210_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2249_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_a_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_a_2229_ = lean_array_uget_borrowed(v_as_2207_, v_i_2209_);
v___x_2230_ = lean_box(0);
v___x_2231_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2225_, v_a_2229_, v___x_2230_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec_ref_known(v___x_2231_, 1);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_nat_add(v_snd_2225_, v___x_2233_);
lean_dec(v_snd_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v___x_2234_);
lean_ctor_set(v___x_2227_, 0, v___x_2232_);
v___x_2236_ = v___x_2227_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
size_t v___x_2237_; size_t v___x_2238_; 
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2209_, v___x_2237_);
v_i_2209_ = v___x_2238_;
v_b_2210_ = v___x_2236_;
goto _start;
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_del_object(v___x_2227_);
lean_dec(v_snd_2225_);
v_a_2241_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2231_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2231_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_2251_, lean_object* v_sz_2252_, lean_object* v_i_2253_, lean_object* v_b_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2252_);
lean_dec(v_sz_2252_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_2251_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v_as_2251_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_2270_, size_t v_sz_2271_, size_t v_i_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_usize_dec_lt(v_i_2272_, v_sz_2271_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_b_2273_);
return v___x_2287_;
}
else
{
lean_object* v_snd_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2312_; 
v_snd_2288_ = lean_ctor_get(v_b_2273_, 1);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_b_2273_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v_b_2273_, 0);
lean_dec(v_unused_2313_);
v___x_2290_ = v_b_2273_;
v_isShared_2291_ = v_isSharedCheck_2312_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_snd_2288_);
lean_dec(v_b_2273_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2312_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_a_2292_ = lean_array_uget_borrowed(v_as_2270_, v_i_2272_);
v___x_2293_ = lean_box(0);
v___x_2294_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2288_, v_a_2292_, v___x_2293_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
lean_dec_ref_known(v___x_2294_, 1);
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_nat_add(v_snd_2288_, v___x_2296_);
lean_dec(v_snd_2288_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 1, v___x_2297_);
lean_ctor_set(v___x_2290_, 0, v___x_2295_);
v___x_2299_ = v___x_2290_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
size_t v___x_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2272_, v___x_2300_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_2270_, v_sz_2271_, v___x_2301_, v___x_2299_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2302_;
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_del_object(v___x_2290_);
lean_dec(v_snd_2288_);
v_a_2304_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2294_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2294_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_2314_, lean_object* v_sz_2315_, lean_object* v_i_2316_, lean_object* v_b_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
size_t v_sz_boxed_2330_; size_t v_i_boxed_2331_; lean_object* v_res_2332_; 
v_sz_boxed_2330_ = lean_unbox_usize(v_sz_2315_);
lean_dec(v_sz_2315_);
v_i_boxed_2331_ = lean_unbox_usize(v_i_2316_);
lean_dec(v_i_2316_);
v_res_2332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_as_2314_, v_sz_boxed_2330_, v_i_boxed_2331_, v_b_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v_as_2314_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_2333_, size_t v_sz_2334_, size_t v_i_2335_, lean_object* v_b_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_usize_dec_lt(v_i_2335_, v_sz_2334_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_b_2336_);
return v___x_2350_;
}
else
{
lean_object* v_snd_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2375_; 
v_snd_2351_ = lean_ctor_get(v_b_2336_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_b_2336_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v_b_2336_, 0);
lean_dec(v_unused_2376_);
v___x_2353_ = v_b_2336_;
v_isShared_2354_ = v_isSharedCheck_2375_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_snd_2351_);
lean_dec(v_b_2336_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2375_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_a_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_a_2355_ = lean_array_uget_borrowed(v_as_2333_, v_i_2335_);
v___x_2356_ = lean_box(0);
v___x_2357_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2351_, v_a_2355_, v___x_2356_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_dec_ref_known(v___x_2357_, 1);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_nat_add(v_snd_2351_, v___x_2359_);
lean_dec(v_snd_2351_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v___x_2360_);
lean_ctor_set(v___x_2353_, 0, v___x_2358_);
v___x_2362_ = v___x_2353_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
size_t v___x_2363_; size_t v___x_2364_; 
v___x_2363_ = ((size_t)1ULL);
v___x_2364_ = lean_usize_add(v_i_2335_, v___x_2363_);
v_i_2335_ = v___x_2364_;
v_b_2336_ = v___x_2362_;
goto _start;
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_del_object(v___x_2353_);
lean_dec(v_snd_2351_);
v_a_2367_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2357_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2357_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_2377_, lean_object* v_sz_2378_, lean_object* v_i_2379_, lean_object* v_b_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
size_t v_sz_boxed_2393_; size_t v_i_boxed_2394_; lean_object* v_res_2395_; 
v_sz_boxed_2393_ = lean_unbox_usize(v_sz_2378_);
lean_dec(v_sz_2378_);
v_i_boxed_2394_ = lean_unbox_usize(v_i_2379_);
lean_dec(v_i_2379_);
v_res_2395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_2377_, v_sz_boxed_2393_, v_i_boxed_2394_, v_b_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v_as_2377_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_2396_, size_t v_sz_2397_, size_t v_i_2398_, lean_object* v_b_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v___x_2412_; 
v___x_2412_ = lean_usize_dec_lt(v_i_2398_, v_sz_2397_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_b_2399_);
return v___x_2413_;
}
else
{
lean_object* v_snd_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2438_; 
v_snd_2414_ = lean_ctor_get(v_b_2399_, 1);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_b_2399_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; 
v_unused_2439_ = lean_ctor_get(v_b_2399_, 0);
lean_dec(v_unused_2439_);
v___x_2416_ = v_b_2399_;
v_isShared_2417_ = v_isSharedCheck_2438_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_snd_2414_);
lean_dec(v_b_2399_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2438_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_a_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_a_2418_ = lean_array_uget_borrowed(v_as_2396_, v_i_2398_);
v___x_2419_ = lean_box(0);
v___x_2420_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2414_, v_a_2418_, v___x_2419_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_dec_ref_known(v___x_2420_, 1);
v___x_2421_ = lean_box(0);
v___x_2422_ = lean_unsigned_to_nat(1u);
v___x_2423_ = lean_nat_add(v_snd_2414_, v___x_2422_);
lean_dec(v_snd_2414_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2423_);
lean_ctor_set(v___x_2416_, 0, v___x_2421_);
v___x_2425_ = v___x_2416_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
size_t v___x_2426_; size_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = ((size_t)1ULL);
v___x_2427_ = lean_usize_add(v_i_2398_, v___x_2426_);
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_2396_, v_sz_2397_, v___x_2427_, v___x_2425_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2428_;
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_del_object(v___x_2416_);
lean_dec(v_snd_2414_);
v_a_2430_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2420_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2420_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_2440_, lean_object* v_sz_2441_, lean_object* v_i_2442_, lean_object* v_b_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
size_t v_sz_boxed_2456_; size_t v_i_boxed_2457_; lean_object* v_res_2458_; 
v_sz_boxed_2456_ = lean_unbox_usize(v_sz_2441_);
lean_dec(v_sz_2441_);
v_i_boxed_2457_ = lean_unbox_usize(v_i_2442_);
lean_dec(v_i_2442_);
v_res_2458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_2440_, v_sz_boxed_2456_, v_i_boxed_2457_, v_b_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v_as_2440_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_init_2459_, lean_object* v_n_2460_, lean_object* v_b_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
if (lean_obj_tag(v_n_2460_) == 0)
{
lean_object* v_cs_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; size_t v_sz_2477_; size_t v___x_2478_; lean_object* v___x_2479_; 
v_cs_2474_ = lean_ctor_get(v_n_2460_, 0);
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v_b_2461_);
v_sz_2477_ = lean_array_size(v_cs_2474_);
v___x_2478_ = ((size_t)0ULL);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_2459_, v_cs_2474_, v_sz_2477_, v___x_2478_, v___x_2476_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2494_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2494_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2494_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_fst_2484_; 
v_fst_2484_ = lean_ctor_get(v_a_2480_, 0);
if (lean_obj_tag(v_fst_2484_) == 0)
{
lean_object* v_snd_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v_snd_2485_ = lean_ctor_get(v_a_2480_, 1);
lean_inc(v_snd_2485_);
lean_dec(v_a_2480_);
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v_snd_2485_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2486_);
v___x_2488_ = v___x_2482_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
else
{
lean_object* v_val_2490_; lean_object* v___x_2492_; 
lean_inc_ref(v_fst_2484_);
lean_dec(v_a_2480_);
v_val_2490_ = lean_ctor_get(v_fst_2484_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v_fst_2484_, 1);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v_val_2490_);
v___x_2492_ = v___x_2482_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_val_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v_a_2495_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2479_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2479_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v_vs_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; size_t v_sz_2506_; size_t v___x_2507_; lean_object* v___x_2508_; 
v_vs_2503_ = lean_ctor_get(v_n_2460_, 0);
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
lean_ctor_set(v___x_2505_, 1, v_b_2461_);
v_sz_2506_ = lean_array_size(v_vs_2503_);
v___x_2507_ = ((size_t)0ULL);
v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_2503_, v_sz_2506_, v___x_2507_, v___x_2505_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2523_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2523_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2523_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_fst_2513_; 
v_fst_2513_ = lean_ctor_get(v_a_2509_, 0);
if (lean_obj_tag(v_fst_2513_) == 0)
{
lean_object* v_snd_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v_snd_2514_ = lean_ctor_get(v_a_2509_, 1);
lean_inc(v_snd_2514_);
lean_dec(v_a_2509_);
v___x_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_snd_2514_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2515_);
v___x_2517_ = v___x_2511_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
else
{
lean_object* v_val_2519_; lean_object* v___x_2521_; 
lean_inc_ref(v_fst_2513_);
lean_dec(v_a_2509_);
v_val_2519_ = lean_ctor_get(v_fst_2513_, 0);
lean_inc(v_val_2519_);
lean_dec_ref_known(v_fst_2513_, 1);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_val_2519_);
v___x_2521_ = v___x_2511_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_val_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_a_2524_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2508_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2508_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_init_2532_, lean_object* v_as_2533_, size_t v_sz_2534_, size_t v_i_2535_, lean_object* v_b_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
uint8_t v___x_2549_; 
v___x_2549_ = lean_usize_dec_lt(v_i_2535_, v_sz_2534_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_b_2536_);
return v___x_2550_;
}
else
{
lean_object* v_snd_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2585_; 
v_snd_2551_ = lean_ctor_get(v_b_2536_, 1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_b_2536_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v_b_2536_, 0);
lean_dec(v_unused_2586_);
v___x_2553_ = v_b_2536_;
v_isShared_2554_ = v_isSharedCheck_2585_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_snd_2551_);
lean_dec(v_b_2536_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2585_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v_a_2555_; lean_object* v___x_2556_; 
v_a_2555_ = lean_array_uget_borrowed(v_as_2533_, v_i_2535_);
lean_inc(v_snd_2551_);
v___x_2556_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_2532_, v_a_2555_, v_snd_2551_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2576_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2576_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2576_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
if (lean_obj_tag(v_a_2557_) == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_a_2557_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2561_);
v___x_2563_ = v___x_2553_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_snd_2551_);
v___x_2563_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
lean_object* v___x_2565_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2563_);
v___x_2565_ = v___x_2559_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
lean_del_object(v___x_2559_);
lean_dec(v_snd_2551_);
v_a_2568_ = lean_ctor_get(v_a_2557_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v_a_2557_, 1);
v___x_2569_ = lean_box(0);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 1, v_a_2568_);
lean_ctor_set(v___x_2553_, 0, v___x_2569_);
v___x_2571_ = v___x_2553_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_a_2568_);
v___x_2571_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
size_t v___x_2572_; size_t v___x_2573_; 
v___x_2572_ = ((size_t)1ULL);
v___x_2573_ = lean_usize_add(v_i_2535_, v___x_2572_);
v_i_2535_ = v___x_2573_;
v_b_2536_ = v___x_2571_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_del_object(v___x_2553_);
lean_dec(v_snd_2551_);
v_a_2577_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2556_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2556_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_init_2587_ = _args[0];
lean_object* v_as_2588_ = _args[1];
lean_object* v_sz_2589_ = _args[2];
lean_object* v_i_2590_ = _args[3];
lean_object* v_b_2591_ = _args[4];
lean_object* v___y_2592_ = _args[5];
lean_object* v___y_2593_ = _args[6];
lean_object* v___y_2594_ = _args[7];
lean_object* v___y_2595_ = _args[8];
lean_object* v___y_2596_ = _args[9];
lean_object* v___y_2597_ = _args[10];
lean_object* v___y_2598_ = _args[11];
lean_object* v___y_2599_ = _args[12];
lean_object* v___y_2600_ = _args[13];
lean_object* v___y_2601_ = _args[14];
lean_object* v___y_2602_ = _args[15];
lean_object* v___y_2603_ = _args[16];
_start:
{
size_t v_sz_boxed_2604_; size_t v_i_boxed_2605_; lean_object* v_res_2606_; 
v_sz_boxed_2604_ = lean_unbox_usize(v_sz_2589_);
lean_dec(v_sz_2589_);
v_i_boxed_2605_ = lean_unbox_usize(v_i_2590_);
lean_dec(v_i_2590_);
v_res_2606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_2587_, v_as_2588_, v_sz_boxed_2604_, v_i_boxed_2605_, v_b_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v_as_2588_);
lean_dec(v_init_2587_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_init_2607_, lean_object* v_n_2608_, lean_object* v_b_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_2607_, v_n_2608_, v_b_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v_n_2608_);
lean_dec(v_init_2607_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(lean_object* v_t_2623_, lean_object* v_init_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_root_2637_; lean_object* v_tail_2638_; lean_object* v___x_2639_; 
v_root_2637_ = lean_ctor_get(v_t_2623_, 0);
v_tail_2638_ = lean_ctor_get(v_t_2623_, 1);
lean_inc(v_init_2624_);
v___x_2639_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_2624_, v_root_2637_, v_init_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v_init_2624_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2676_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2676_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2676_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
if (lean_obj_tag(v_a_2640_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; 
v_a_2644_ = lean_ctor_get(v_a_2640_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v_a_2640_, 1);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_a_2644_);
v___x_2646_ = v___x_2642_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; size_t v_sz_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
lean_del_object(v___x_2642_);
v_a_2648_ = lean_ctor_get(v_a_2640_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v_a_2640_, 1);
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v_a_2648_);
v_sz_2651_ = lean_array_size(v_tail_2638_);
v___x_2652_ = ((size_t)0ULL);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_tail_2638_, v_sz_2651_, v___x_2652_, v___x_2650_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2667_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2667_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2667_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_fst_2658_; 
v_fst_2658_ = lean_ctor_get(v_a_2654_, 0);
if (lean_obj_tag(v_fst_2658_) == 0)
{
lean_object* v_snd_2659_; lean_object* v___x_2661_; 
v_snd_2659_ = lean_ctor_get(v_a_2654_, 1);
lean_inc(v_snd_2659_);
lean_dec(v_a_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_snd_2659_);
v___x_2661_ = v___x_2656_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_snd_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2665_; 
lean_inc_ref(v_fst_2658_);
lean_dec(v_a_2654_);
v_val_2663_ = lean_ctor_get(v_fst_2658_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v_fst_2658_, 1);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_val_2663_);
v___x_2665_ = v___x_2656_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_val_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_a_2668_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2653_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2653_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
v_a_2677_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2639_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2639_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_2685_, lean_object* v_init_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_t_2685_, v_init_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v_t_2685_);
return v_res_2699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1));
v___x_2703_ = lean_unsigned_to_nat(2u);
v___x_2704_ = lean_unsigned_to_nat(73u);
v___x_2705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0));
v___x_2706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2707_ = l_mkPanicMessageWithDecl(v___x_2706_, v___x_2705_, v___x_2704_, v___x_2703_, v___x_2702_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v_vars_2722_; lean_object* v_diseqs_2723_; lean_object* v_size_2724_; lean_object* v_size_2725_; uint8_t v___x_2726_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v_vars_2722_ = lean_ctor_get(v_a_2721_, 30);
lean_inc_ref(v_vars_2722_);
v_diseqs_2723_ = lean_ctor_get(v_a_2721_, 34);
lean_inc_ref(v_diseqs_2723_);
lean_dec(v_a_2721_);
v_size_2724_ = lean_ctor_get(v_vars_2722_, 2);
lean_inc(v_size_2724_);
lean_dec_ref(v_vars_2722_);
v_size_2725_ = lean_ctor_get(v_diseqs_2723_, 2);
v___x_2726_ = lean_nat_dec_eq(v_size_2724_, v_size_2725_);
lean_dec(v_size_2724_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec_ref(v_diseqs_2723_);
v___x_2727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2);
v___x_2728_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_2727_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_diseqs_2723_, v___x_2729_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec_ref(v_diseqs_2723_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2738_; 
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2738_ == 0)
{
lean_object* v_unused_2739_; 
v_unused_2739_ = lean_ctor_get(v___x_2730_, 0);
lean_dec(v_unused_2739_);
v___x_2732_ = v___x_2730_;
v_isShared_2733_ = v_isSharedCheck_2738_;
goto v_resetjp_2731_;
}
else
{
lean_dec(v___x_2730_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2738_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_box(0);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2734_);
v___x_2736_ = v___x_2732_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
v_a_2740_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2730_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2730_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_a_2748_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2720_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2720_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___boxed(lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec(v_a_2756_);
return v_res_2768_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2783_; lean_object* v___f_2784_; lean_object* v___x_4704__overap_2785_; lean_object* v___x_2786_; 
v___x_2783_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0);
v___f_2784_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2784_, 0, v___x_2783_);
v___x_4704__overap_2785_ = lean_panic_fn_borrowed(v___f_2784_, v_msg_2770_);
lean_dec_ref(v___f_2784_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc_ref(v___y_2778_);
lean_inc(v___y_2777_);
lean_inc_ref(v___y_2776_);
lean_inc(v___y_2775_);
lean_inc_ref(v___y_2774_);
lean_inc(v___y_2773_);
lean_inc(v___y_2772_);
lean_inc(v___y_2771_);
v___x_2786_ = lean_apply_12(v___x_4704__overap_2785_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, lean_box(0));
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___boxed(lean_object* v_msg_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v_msg_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec(v___y_2788_);
return v_res_2800_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3));
v___x_2803_ = lean_unsigned_to_nat(6u);
v___x_2804_ = lean_unsigned_to_nat(89u);
v___x_2805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_2806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2807_ = l_mkPanicMessageWithDecl(v___x_2806_, v___x_2805_, v___x_2804_, v___x_2803_, v___x_2802_);
return v___x_2807_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2));
v___x_2810_ = lean_unsigned_to_nat(6u);
v___x_2811_ = lean_unsigned_to_nat(87u);
v___x_2812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_2813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2814_ = l_mkPanicMessageWithDecl(v___x_2813_, v___x_2812_, v___x_2811_, v___x_2810_, v___x_2809_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(lean_object* v_vars_2815_, lean_object* v___x_2816_, lean_object* v_x_2817_, lean_object* v_____s_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_fst_2836_; lean_object* v_snd_2837_; lean_object* v_size_2838_; uint8_t v___x_2839_; 
v_fst_2836_ = lean_ctor_get(v_x_2817_, 0);
v_snd_2837_ = lean_ctor_get(v_x_2817_, 1);
v_size_2838_ = lean_ctor_get(v_vars_2815_, 2);
v___x_2839_ = lean_nat_dec_lt(v_snd_2837_, v_size_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1);
v___x_2841_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_2840_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_dec_ref_known(v___x_2841_, 1);
goto v___jp_2831_;
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; uint8_t v___x_2853_; 
v___x_2850_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2816_, v_vars_2815_, v_snd_2837_);
v___x_2851_ = lean_ptr_addr(v_fst_2836_);
v___x_2852_ = lean_ptr_addr(v___x_2850_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_usize_dec_eq(v___x_2851_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3);
v___x_2855_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v___x_2854_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
return v___x_2855_;
}
else
{
goto v___jp_2831_;
}
}
v___jp_2831_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2832_ = lean_unsigned_to_nat(1u);
v___x_2833_ = lean_nat_add(v_____s_2818_, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed(lean_object* v_vars_2856_, lean_object* v___x_2857_, lean_object* v_x_2858_, lean_object* v_____s_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(v_vars_2856_, v___x_2857_, v_x_2858_, v_____s_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec(v_____s_2859_);
lean_dec_ref(v_x_2858_);
lean_dec_ref(v___x_2857_);
lean_dec_ref(v_vars_2856_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(lean_object* v_f_2873_, lean_object* v_s_2874_, lean_object* v_a_2875_, lean_object* v_b_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_a_2875_);
lean_ctor_set(v___x_2889_, 1, v_b_2876_);
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc(v___y_2885_);
lean_inc_ref(v___y_2884_);
lean_inc(v___y_2883_);
lean_inc_ref(v___y_2882_);
lean_inc(v___y_2881_);
lean_inc_ref(v___y_2880_);
lean_inc(v___y_2879_);
lean_inc(v___y_2878_);
lean_inc(v___y_2877_);
v___x_2890_ = lean_apply_14(v_f_2873_, v___x_2889_, v_s_2874_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, lean_box(0));
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2917_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2917_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2917_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
if (lean_obj_tag(v_a_2891_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2905_; 
v_a_2895_ = lean_ctor_get(v_a_2891_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_a_2891_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2897_ = v_a_2891_;
v_isShared_2898_ = v_isSharedCheck_2905_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v_a_2891_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2905_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2902_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2900_);
v___x_2902_ = v___x_2893_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2916_; 
v_a_2906_ = lean_ctor_get(v_a_2891_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_a_2891_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2908_ = v_a_2891_;
v_isShared_2909_ = v_isSharedCheck_2916_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v_a_2891_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2916_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2913_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2911_);
v___x_2913_ = v___x_2893_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
v_a_2918_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2890_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2890_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed(lean_object* v_f_2926_, lean_object* v_s_2927_, lean_object* v_a_2928_, lean_object* v_b_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(v_f_2926_, v_s_2927_, v_a_2928_, v_b_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec(v___y_2930_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_2943_, lean_object* v_keys_2944_, lean_object* v_vals_2945_, lean_object* v_i_2946_, lean_object* v_acc_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = lean_array_get_size(v_keys_2944_);
v___x_2961_ = lean_nat_dec_lt(v_i_2946_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
lean_dec(v_i_2946_);
lean_dec_ref(v_f_2943_);
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v_acc_2947_);
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
else
{
lean_object* v_k_2964_; lean_object* v_v_2965_; lean_object* v___x_2966_; 
v_k_2964_ = lean_array_fget_borrowed(v_keys_2944_, v_i_2946_);
v_v_2965_ = lean_array_fget_borrowed(v_vals_2945_, v_i_2946_);
lean_inc_ref(v_f_2943_);
lean_inc(v___y_2958_);
lean_inc_ref(v___y_2957_);
lean_inc(v___y_2956_);
lean_inc_ref(v___y_2955_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
lean_inc(v___y_2950_);
lean_inc(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc(v_v_2965_);
lean_inc(v_k_2964_);
v___x_2966_ = lean_apply_15(v_f_2943_, v_acc_2947_, v_k_2964_, v_v_2965_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, lean_box(0));
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
if (lean_obj_tag(v_a_2967_) == 0)
{
lean_dec_ref_known(v_a_2967_, 1);
lean_dec(v_i_2946_);
lean_dec_ref(v_f_2943_);
return v___x_2966_;
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2966_, 1);
v_a_2968_ = lean_ctor_get(v_a_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v_a_2967_, 1);
v___x_2969_ = lean_unsigned_to_nat(1u);
v___x_2970_ = lean_nat_add(v_i_2946_, v___x_2969_);
lean_dec(v_i_2946_);
v_i_2946_ = v___x_2970_;
v_acc_2947_ = v_a_2968_;
goto _start;
}
}
else
{
lean_dec(v_i_2946_);
lean_dec_ref(v_f_2943_);
return v___x_2966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_f_2972_ = _args[0];
lean_object* v_keys_2973_ = _args[1];
lean_object* v_vals_2974_ = _args[2];
lean_object* v_i_2975_ = _args[3];
lean_object* v_acc_2976_ = _args[4];
lean_object* v___y_2977_ = _args[5];
lean_object* v___y_2978_ = _args[6];
lean_object* v___y_2979_ = _args[7];
lean_object* v___y_2980_ = _args[8];
lean_object* v___y_2981_ = _args[9];
lean_object* v___y_2982_ = _args[10];
lean_object* v___y_2983_ = _args[11];
lean_object* v___y_2984_ = _args[12];
lean_object* v___y_2985_ = _args[13];
lean_object* v___y_2986_ = _args[14];
lean_object* v___y_2987_ = _args[15];
lean_object* v___y_2988_ = _args[16];
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_2972_, v_keys_2973_, v_vals_2974_, v_i_2975_, v_acc_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v_vals_2974_);
lean_dec_ref(v_keys_2973_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_2990_, lean_object* v_as_2991_, size_t v_i_2992_, size_t v_stop_2993_, lean_object* v_b_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_a_3008_; lean_object* v___y_3013_; uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_eq(v_i_2992_, v_stop_2993_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_array_uget_borrowed(v_as_2991_, v_i_2992_);
switch(lean_obj_tag(v___x_3017_))
{
case 0:
{
lean_object* v_key_3018_; lean_object* v_val_3019_; lean_object* v___x_3020_; 
v_key_3018_ = lean_ctor_get(v___x_3017_, 0);
v_val_3019_ = lean_ctor_get(v___x_3017_, 1);
lean_inc_ref(v_f_2990_);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
lean_inc(v___y_2997_);
lean_inc(v___y_2996_);
lean_inc(v___y_2995_);
lean_inc(v_val_3019_);
lean_inc(v_key_3018_);
v___x_3020_ = lean_apply_15(v_f_2990_, v_b_2994_, v_key_3018_, v_val_3019_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, lean_box(0));
v___y_3013_ = v___x_3020_;
goto v___jp_3012_;
}
case 1:
{
lean_object* v_node_3021_; lean_object* v___x_3022_; 
v_node_3021_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_node_3021_);
lean_inc_ref(v_f_2990_);
v___x_3022_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_2990_, v_node_3021_, v_b_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
v___y_3013_ = v___x_3022_;
goto v___jp_3012_;
}
default: 
{
v_a_3008_ = v_b_2994_;
goto v___jp_3007_;
}
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
lean_dec_ref(v_f_2990_);
v___x_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_b_2994_);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
return v___x_3024_;
}
v___jp_3007_:
{
size_t v___x_3009_; size_t v___x_3010_; 
v___x_3009_ = ((size_t)1ULL);
v___x_3010_ = lean_usize_add(v_i_2992_, v___x_3009_);
v_i_2992_ = v___x_3010_;
v_b_2994_ = v_a_3008_;
goto _start;
}
v___jp_3012_:
{
if (lean_obj_tag(v___y_3013_) == 0)
{
lean_object* v_a_3014_; 
v_a_3014_ = lean_ctor_get(v___y_3013_, 0);
if (lean_obj_tag(v_a_3014_) == 0)
{
lean_dec_ref(v_f_2990_);
return v___y_3013_;
}
else
{
lean_object* v_a_3015_; 
lean_inc_ref(v_a_3014_);
lean_dec_ref_known(v___y_3013_, 1);
v_a_3015_ = lean_ctor_get(v_a_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v_a_3014_, 1);
v_a_3008_ = v_a_3015_;
goto v___jp_3007_;
}
}
else
{
lean_dec_ref(v_f_2990_);
return v___y_3013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(lean_object* v_f_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
if (lean_obj_tag(v_x_3026_) == 0)
{
lean_object* v_es_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3054_; 
v_es_3040_ = lean_ctor_get(v_x_3026_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_x_3026_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3042_ = v_x_3026_;
v_isShared_3043_ = v_isSharedCheck_3054_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_es_3040_);
lean_dec(v_x_3026_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3054_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3045_ = lean_array_get_size(v_es_3040_);
v___x_3046_ = lean_nat_dec_lt(v___x_3044_, v___x_3045_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3048_; 
lean_dec_ref(v_es_3040_);
lean_dec_ref(v_f_3025_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set_tag(v___x_3042_, 1);
lean_ctor_set(v___x_3042_, 0, v_x_3027_);
v___x_3048_ = v___x_3042_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_x_3027_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
return v___x_3049_;
}
}
else
{
size_t v___x_3051_; size_t v___x_3052_; lean_object* v___x_3053_; 
lean_del_object(v___x_3042_);
v___x_3051_ = ((size_t)0ULL);
v___x_3052_ = lean_usize_of_nat(v___x_3045_);
v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3025_, v_es_3040_, v___x_3051_, v___x_3052_, v_x_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec_ref(v_es_3040_);
return v___x_3053_;
}
}
}
else
{
lean_object* v_ks_3055_; lean_object* v_vs_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_ks_3055_ = lean_ctor_get(v_x_3026_, 0);
lean_inc_ref(v_ks_3055_);
v_vs_3056_ = lean_ctor_get(v_x_3026_, 1);
lean_inc_ref(v_vs_3056_);
lean_dec_ref_known(v_x_3026_, 2);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3025_, v_ks_3055_, v_vs_3056_, v___x_3057_, v_x_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec_ref(v_vs_3056_);
lean_dec_ref(v_ks_3055_);
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_3059_, lean_object* v_x_3060_, lean_object* v_x_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3059_, v_x_3060_, v_x_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec(v___y_3062_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object** _args){
lean_object* v_f_3075_ = _args[0];
lean_object* v_as_3076_ = _args[1];
lean_object* v_i_3077_ = _args[2];
lean_object* v_stop_3078_ = _args[3];
lean_object* v_b_3079_ = _args[4];
lean_object* v___y_3080_ = _args[5];
lean_object* v___y_3081_ = _args[6];
lean_object* v___y_3082_ = _args[7];
lean_object* v___y_3083_ = _args[8];
lean_object* v___y_3084_ = _args[9];
lean_object* v___y_3085_ = _args[10];
lean_object* v___y_3086_ = _args[11];
lean_object* v___y_3087_ = _args[12];
lean_object* v___y_3088_ = _args[13];
lean_object* v___y_3089_ = _args[14];
lean_object* v___y_3090_ = _args[15];
lean_object* v___y_3091_ = _args[16];
_start:
{
size_t v_i_boxed_3092_; size_t v_stop_boxed_3093_; lean_object* v_res_3094_; 
v_i_boxed_3092_ = lean_unbox_usize(v_i_3077_);
lean_dec(v_i_3077_);
v_stop_boxed_3093_ = lean_unbox_usize(v_stop_3078_);
lean_dec(v_stop_3078_);
v_res_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3075_, v_as_3076_, v_i_boxed_3092_, v_stop_boxed_3093_, v_b_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v_as_3076_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(lean_object* v_map_3095_, lean_object* v_init_3096_, lean_object* v_f_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___f_3110_; lean_object* v___x_3111_; 
v___f_3110_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed), 16, 1);
lean_closure_set(v___f_3110_, 0, v_f_3097_);
lean_inc_ref(v_map_3095_);
v___x_3111_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v___f_3110_, v_map_3095_, v_init_3096_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v_a_3116_; lean_object* v___x_3118_; 
v_a_3116_ = lean_ctor_get(v_a_3112_, 0);
lean_inc(v_a_3116_);
lean_dec(v_a_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v_a_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3111_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3111_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___boxed(lean_object* v_map_3129_, lean_object* v_init_3130_, lean_object* v_f_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_3129_, v_init_3130_, v_f_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v_map_3129_);
return v_res_3144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0));
v___x_3147_ = lean_unsigned_to_nat(2u);
v___x_3148_ = lean_unsigned_to_nat(91u);
v___x_3149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_3150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_3151_ = l_mkPanicMessageWithDecl(v___x_3150_, v___x_3149_, v___x_3148_, v___x_3147_, v___x_3146_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v_vars_3166_; lean_object* v_varMap_3167_; lean_object* v___x_3168_; lean_object* v___f_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v_vars_3166_ = lean_ctor_get(v_a_3165_, 30);
lean_inc_ref_n(v_vars_3166_, 2);
v_varMap_3167_ = lean_ctor_get(v_a_3165_, 31);
lean_inc_ref(v_varMap_3167_);
lean_dec(v_a_3165_);
v___x_3168_ = l_Lean_instInhabitedExpr;
v___f_3169_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed), 16, 2);
lean_closure_set(v___f_3169_, 0, v_vars_3166_);
lean_closure_set(v___f_3169_, 1, v___x_3168_);
v___x_3170_ = lean_unsigned_to_nat(0u);
v___x_3171_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_varMap_3167_, v___x_3170_, v___f_3169_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
lean_dec_ref(v_varMap_3167_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3184_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_size_3176_; uint8_t v___x_3177_; 
v_size_3176_ = lean_ctor_get(v_vars_3166_, 2);
lean_inc(v_size_3176_);
lean_dec_ref(v_vars_3166_);
v___x_3177_ = lean_nat_dec_eq(v_size_3176_, v_a_3172_);
lean_dec(v_a_3172_);
lean_dec(v_size_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_del_object(v___x_3174_);
v___x_3178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1);
v___x_3179_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3178_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
return v___x_3179_;
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = lean_box(0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3180_);
v___x_3182_ = v___x_3174_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref(v_vars_3166_);
v_a_3185_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3171_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3171_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
v_a_3193_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3164_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3164_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___boxed(lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec(v_a_3201_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(lean_object* v_00_u03c3_3214_, lean_object* v_00_u03b2_3215_, lean_object* v_map_3216_, lean_object* v_init_3217_, lean_object* v_f_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_3216_, v_init_3217_, v_f_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_3232_ = _args[0];
lean_object* v_00_u03b2_3233_ = _args[1];
lean_object* v_map_3234_ = _args[2];
lean_object* v_init_3235_ = _args[3];
lean_object* v_f_3236_ = _args[4];
lean_object* v___y_3237_ = _args[5];
lean_object* v___y_3238_ = _args[6];
lean_object* v___y_3239_ = _args[7];
lean_object* v___y_3240_ = _args[8];
lean_object* v___y_3241_ = _args[9];
lean_object* v___y_3242_ = _args[10];
lean_object* v___y_3243_ = _args[11];
lean_object* v___y_3244_ = _args[12];
lean_object* v___y_3245_ = _args[13];
lean_object* v___y_3246_ = _args[14];
lean_object* v___y_3247_ = _args[15];
lean_object* v___y_3248_ = _args[16];
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(v_00_u03c3_3232_, v_00_u03b2_3233_, v_map_3234_, v_init_3235_, v_f_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v_map_3234_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(lean_object* v_map_3250_, lean_object* v_f_3251_, lean_object* v_init_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3251_, v_map_3250_, v_init_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg___boxed(lean_object* v_map_3266_, lean_object* v_f_3267_, lean_object* v_init_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(v_map_3266_, v_f_3267_, v_init_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(lean_object* v_00_u03c3_3282_, lean_object* v_00_u03c3_3283_, lean_object* v_00_u03b2_3284_, lean_object* v_map_3285_, lean_object* v_f_3286_, lean_object* v_init_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3286_, v_map_3285_, v_init_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_3301_ = _args[0];
lean_object* v_00_u03c3_3302_ = _args[1];
lean_object* v_00_u03b2_3303_ = _args[2];
lean_object* v_map_3304_ = _args[3];
lean_object* v_f_3305_ = _args[4];
lean_object* v_init_3306_ = _args[5];
lean_object* v___y_3307_ = _args[6];
lean_object* v___y_3308_ = _args[7];
lean_object* v___y_3309_ = _args[8];
lean_object* v___y_3310_ = _args[9];
lean_object* v___y_3311_ = _args[10];
lean_object* v___y_3312_ = _args[11];
lean_object* v___y_3313_ = _args[12];
lean_object* v___y_3314_ = _args[13];
lean_object* v___y_3315_ = _args[14];
lean_object* v___y_3316_ = _args[15];
lean_object* v___y_3317_ = _args[16];
lean_object* v___y_3318_ = _args[17];
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(v_00_u03c3_3301_, v_00_u03c3_3302_, v_00_u03b2_3303_, v_map_3304_, v_f_3305_, v_init_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v___y_3307_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_3320_, lean_object* v_00_u03c3_3321_, lean_object* v_00_u03b1_3322_, lean_object* v_00_u03b2_3323_, lean_object* v_f_3324_, lean_object* v_x_3325_, lean_object* v_x_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3324_, v_x_3325_, v_x_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_3340_ = _args[0];
lean_object* v_00_u03c3_3341_ = _args[1];
lean_object* v_00_u03b1_3342_ = _args[2];
lean_object* v_00_u03b2_3343_ = _args[3];
lean_object* v_f_3344_ = _args[4];
lean_object* v_x_3345_ = _args[5];
lean_object* v_x_3346_ = _args[6];
lean_object* v___y_3347_ = _args[7];
lean_object* v___y_3348_ = _args[8];
lean_object* v___y_3349_ = _args[9];
lean_object* v___y_3350_ = _args[10];
lean_object* v___y_3351_ = _args[11];
lean_object* v___y_3352_ = _args[12];
lean_object* v___y_3353_ = _args[13];
lean_object* v___y_3354_ = _args[14];
lean_object* v___y_3355_ = _args[15];
lean_object* v___y_3356_ = _args[16];
lean_object* v___y_3357_ = _args[17];
lean_object* v___y_3358_ = _args[18];
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(v_00_u03c3_3340_, v_00_u03c3_3341_, v_00_u03b1_3342_, v_00_u03b2_3343_, v_f_3344_, v_x_3345_, v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3347_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_3360_, lean_object* v_00_u03b2_3361_, lean_object* v_00_u03c3_3362_, lean_object* v_00_u03c3_3363_, lean_object* v_f_3364_, lean_object* v_as_3365_, size_t v_i_3366_, size_t v_stop_3367_, lean_object* v_b_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3364_, v_as_3365_, v_i_3366_, v_stop_3367_, v_b_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03b1_3382_ = _args[0];
lean_object* v_00_u03b2_3383_ = _args[1];
lean_object* v_00_u03c3_3384_ = _args[2];
lean_object* v_00_u03c3_3385_ = _args[3];
lean_object* v_f_3386_ = _args[4];
lean_object* v_as_3387_ = _args[5];
lean_object* v_i_3388_ = _args[6];
lean_object* v_stop_3389_ = _args[7];
lean_object* v_b_3390_ = _args[8];
lean_object* v___y_3391_ = _args[9];
lean_object* v___y_3392_ = _args[10];
lean_object* v___y_3393_ = _args[11];
lean_object* v___y_3394_ = _args[12];
lean_object* v___y_3395_ = _args[13];
lean_object* v___y_3396_ = _args[14];
lean_object* v___y_3397_ = _args[15];
lean_object* v___y_3398_ = _args[16];
lean_object* v___y_3399_ = _args[17];
lean_object* v___y_3400_ = _args[18];
lean_object* v___y_3401_ = _args[19];
lean_object* v___y_3402_ = _args[20];
_start:
{
size_t v_i_boxed_3403_; size_t v_stop_boxed_3404_; lean_object* v_res_3405_; 
v_i_boxed_3403_ = lean_unbox_usize(v_i_3388_);
lean_dec(v_i_3388_);
v_stop_boxed_3404_ = lean_unbox_usize(v_stop_3389_);
lean_dec(v_stop_3389_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_3382_, v_00_u03b2_3383_, v_00_u03c3_3384_, v_00_u03c3_3385_, v_f_3386_, v_as_3387_, v_i_boxed_3403_, v_stop_boxed_3404_, v_b_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v_as_3387_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_3406_, lean_object* v_00_u03c3_3407_, lean_object* v_00_u03b1_3408_, lean_object* v_00_u03b2_3409_, lean_object* v_f_3410_, lean_object* v_keys_3411_, lean_object* v_vals_3412_, lean_object* v_heq_3413_, lean_object* v_i_3414_, lean_object* v_acc_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3410_, v_keys_3411_, v_vals_3412_, v_i_3414_, v_acc_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03c3_3429_ = _args[0];
lean_object* v_00_u03c3_3430_ = _args[1];
lean_object* v_00_u03b1_3431_ = _args[2];
lean_object* v_00_u03b2_3432_ = _args[3];
lean_object* v_f_3433_ = _args[4];
lean_object* v_keys_3434_ = _args[5];
lean_object* v_vals_3435_ = _args[6];
lean_object* v_heq_3436_ = _args[7];
lean_object* v_i_3437_ = _args[8];
lean_object* v_acc_3438_ = _args[9];
lean_object* v___y_3439_ = _args[10];
lean_object* v___y_3440_ = _args[11];
lean_object* v___y_3441_ = _args[12];
lean_object* v___y_3442_ = _args[13];
lean_object* v___y_3443_ = _args[14];
lean_object* v___y_3444_ = _args[15];
lean_object* v___y_3445_ = _args[16];
lean_object* v___y_3446_ = _args[17];
lean_object* v___y_3447_ = _args[18];
lean_object* v___y_3448_ = _args[19];
lean_object* v___y_3449_ = _args[20];
lean_object* v___y_3450_ = _args[21];
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_3429_, v_00_u03c3_3430_, v_00_u03b1_3431_, v_00_u03b2_3432_, v_f_3433_, v_keys_3434_, v_vals_3435_, v_heq_3436_, v_i_3437_, v_acc_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v_vals_3435_);
lean_dec_ref(v_keys_3434_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3465_; 
lean_dec_ref_known(v___x_3464_, 1);
v___x_3465_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v___x_3466_; 
lean_dec_ref_known(v___x_3465_, 1);
v___x_3466_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref_known(v___x_3466_, 1);
v___x_3467_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
return v___x_3467_;
}
else
{
return v___x_3466_;
}
}
else
{
return v___x_3465_;
}
}
else
{
return v___x_3464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs___boxed(lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec(v_a_3468_);
return v_res_3480_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3483_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1));
v___x_3484_ = lean_unsigned_to_nat(6u);
v___x_3485_ = lean_unsigned_to_nat(103u);
v___x_3486_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0));
v___x_3487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_3488_ = l_mkPanicMessageWithDecl(v___x_3487_, v___x_3486_, v___x_3485_, v___x_3484_, v___x_3483_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(lean_object* v_upperBound_3489_, lean_object* v_a_3490_, lean_object* v_b_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_nat_dec_lt(v_a_3490_, v_upperBound_3489_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; 
lean_dec(v_a_3490_);
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v_b_3491_);
return v___x_3504_;
}
else
{
lean_object* v___x_3505_; lean_object* v___y_3507_; uint8_t v___x_3511_; 
v___x_3505_ = lean_box(0);
v___x_3511_ = lean_nat_dec_eq(v_a_3490_, v_a_3490_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2);
v___x_3513_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3512_, v_a_3490_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
v___y_3507_ = v___x_3513_;
goto v___jp_3506_;
}
else
{
lean_object* v___x_3514_; 
v___x_3514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_3490_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
v___y_3507_ = v___x_3514_;
goto v___jp_3506_;
}
v___jp_3506_:
{
if (lean_obj_tag(v___y_3507_) == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
lean_dec_ref_known(v___y_3507_, 1);
v___x_3508_ = lean_unsigned_to_nat(1u);
v___x_3509_ = lean_nat_add(v_a_3490_, v___x_3508_);
lean_dec(v_a_3490_);
v_a_3490_ = v___x_3509_;
v_b_3491_ = v___x_3505_;
goto _start;
}
else
{
lean_dec(v_a_3490_);
return v___y_3507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___boxed(lean_object* v_upperBound_3515_, lean_object* v_a_3516_, lean_object* v_b_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_3515_, v_a_3516_, v_b_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec(v_upperBound_3515_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants(lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
uint8_t v_debug_3541_; 
v_debug_3541_ = lean_ctor_get_uint8(v_a_3532_, sizeof(void*)*8 + 2);
if (v_debug_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_box(0);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_3530_, v_a_3538_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v_structs_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v_structs_3546_ = lean_ctor_get(v_a_3545_, 0);
lean_inc_ref(v_structs_3546_);
lean_dec(v_a_3545_);
v___x_3547_ = lean_array_get_size(v_structs_3546_);
lean_dec_ref(v_structs_3546_);
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = lean_box(0);
v___x_3550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v___x_3547_, v___x_3548_, v___x_3549_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; 
v_unused_3558_ = lean_ctor_get(v___x_3550_, 0);
lean_dec(v_unused_3558_);
v___x_3552_ = v___x_3550_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_dec(v___x_3550_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3549_);
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3549_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
else
{
return v___x_3550_;
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
v_a_3559_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3544_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3544_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed(lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Meta_Grind_Arith_Linear_checkInvariants(v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec(v_a_3567_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(lean_object* v_upperBound_3579_, lean_object* v_inst_3580_, lean_object* v_R_3581_, lean_object* v_a_3582_, lean_object* v_b_3583_, lean_object* v_c_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_3579_, v_a_3582_, v_b_3583_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_3597_ = _args[0];
lean_object* v_inst_3598_ = _args[1];
lean_object* v_R_3599_ = _args[2];
lean_object* v_a_3600_ = _args[3];
lean_object* v_b_3601_ = _args[4];
lean_object* v_c_3602_ = _args[5];
lean_object* v___y_3603_ = _args[6];
lean_object* v___y_3604_ = _args[7];
lean_object* v___y_3605_ = _args[8];
lean_object* v___y_3606_ = _args[9];
lean_object* v___y_3607_ = _args[10];
lean_object* v___y_3608_ = _args[11];
lean_object* v___y_3609_ = _args[12];
lean_object* v___y_3610_ = _args[13];
lean_object* v___y_3611_ = _args[14];
lean_object* v___y_3612_ = _args[15];
lean_object* v___y_3613_ = _args[16];
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(v_upperBound_3597_, v_inst_3598_, v_R_3599_, v_a_3600_, v_b_3601_, v_c_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec(v_upperBound_3597_);
return v_res_3614_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
}
#ifdef __cplusplus
}
#endif
