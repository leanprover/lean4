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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_k_34_; lean_object* v_p_35_; lean_object* v___x_36_; uint8_t v___x_37_; uint8_t v___x_38_; 
v_k_34_ = lean_ctor_get(v_x_32_, 0);
v_p_35_ = lean_ctor_get(v_x_32_, 2);
v___x_36_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_37_ = lean_int_dec_eq(v_k_34_, v___x_36_);
v___x_38_ = lean_bool_not(v___x_37_);
if (v___x_38_ == 0)
{
return v___x_38_;
}
else
{
v_x_32_ = v_p_35_;
goto _start;
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
lean_object* v___x_57_; lean_object* v___f_58_; lean_object* v___x_2201__overap_59_; lean_object* v___x_60_; 
v___x_57_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0);
v___f_58_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_58_, 0, v___x_57_);
v___x_2201__overap_59_ = lean_panic_fn_borrowed(v___f_58_, v_msg_44_);
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
v___x_60_ = lean_apply_12(v___x_2201__overap_59_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, lean_box(0));
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
lean_object* v_a_210_; uint8_t v___x_211_; uint8_t v___x_212_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = lean_unbox(v_a_210_);
lean_dec(v_a_210_);
v___x_212_ = lean_bool_not(v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2);
v___x_214_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_213_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_214_;
}
else
{
v_p_194_ = v_p_208_;
goto _start;
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_209_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_209_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___boxed(lean_object* v_p_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec(v_a_228_);
lean_dec(v_a_227_);
lean_dec(v_p_226_);
return v_res_239_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1));
v___x_243_ = lean_unsigned_to_nat(2u);
v___x_244_ = lean_unsigned_to_nat(49u);
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0));
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_247_ = l_mkPanicMessageWithDecl(v___x_246_, v___x_245_, v___x_244_, v___x_243_, v___x_242_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3));
v___x_250_ = lean_unsigned_to_nat(24u);
v___x_251_ = lean_unsigned_to_nat(48u);
v___x_252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0));
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_254_ = l_mkPanicMessageWithDecl(v___x_253_, v___x_252_, v___x_251_, v___x_250_, v___x_249_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5));
v___x_257_ = lean_unsigned_to_nat(2u);
v___x_258_ = lean_unsigned_to_nat(42u);
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0));
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_261_ = l_mkPanicMessageWithDecl(v___x_260_, v___x_259_, v___x_258_, v___x_257_, v___x_256_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7));
v___x_264_ = lean_unsigned_to_nat(2u);
v___x_265_ = lean_unsigned_to_nat(43u);
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0));
v___x_267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_268_ = l_mkPanicMessageWithDecl(v___x_267_, v___x_266_, v___x_265_, v___x_264_, v___x_263_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(lean_object* v_p_269_, lean_object* v_x_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; uint8_t v___x_303_; 
v___x_303_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(v_p_269_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6);
v___x_305_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_304_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_305_;
}
else
{
uint8_t v___x_306_; 
v___x_306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(v_p_269_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8);
v___x_308_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_307_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; uint8_t v___x_311_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v___x_311_ = lean_unbox(v_a_310_);
lean_dec(v_a_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_269_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; 
lean_dec_ref_known(v___x_312_, 1);
v___x_313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(v_p_269_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_dec_ref_known(v___x_313_, 1);
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
v___y_294_ = v_a_281_;
goto v___jp_283_;
}
else
{
return v___x_313_;
}
}
else
{
return v___x_312_;
}
}
else
{
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
v___y_294_ = v_a_281_;
goto v___jp_283_;
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_309_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_309_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
v___jp_283_:
{
if (lean_obj_tag(v_p_269_) == 1)
{
lean_object* v_v_295_; uint8_t v___x_296_; 
v_v_295_ = lean_ctor_get(v_p_269_, 1);
v___x_296_ = lean_nat_dec_eq(v_x_270_, v_v_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2);
v___x_298_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_297_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_box(0);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4);
v___x_302_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_301_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___boxed(lean_object* v_p_322_, lean_object* v_x_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_322_, v_x_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_x_323_);
lean_dec(v_p_322_);
return v_res_336_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(lean_object* v_msg_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___f_352_; lean_object* v___x_4606__overap_353_; lean_object* v___x_354_; 
v___x_351_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0);
v___f_352_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_352_, 0, v___x_351_);
v___x_4606__overap_353_ = lean_panic_fn_borrowed(v___f_352_, v_msg_338_);
lean_dec_ref(v___f_352_);
lean_inc(v___y_349_);
lean_inc_ref(v___y_348_);
lean_inc(v___y_347_);
lean_inc_ref(v___y_346_);
lean_inc(v___y_345_);
lean_inc_ref(v___y_344_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc(v___y_340_);
lean_inc(v___y_339_);
v___x_354_ = lean_apply_12(v___x_4606__overap_353_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, lean_box(0));
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___boxed(lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v_msg_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec(v___y_357_);
lean_dec(v___y_356_);
return v_res_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1));
v___x_372_ = lean_unsigned_to_nat(6u);
v___x_373_ = lean_unsigned_to_nat(57u);
v___x_374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0));
v___x_375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_376_ = l_mkPanicMessageWithDecl(v___x_375_, v___x_374_, v___x_373_, v___x_372_, v___x_371_);
return v___x_376_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3));
v___x_378_ = lean_unsigned_to_nat(30u);
v___x_379_ = lean_unsigned_to_nat(56u);
v___x_380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0));
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_382_ = l_mkPanicMessageWithDecl(v___x_381_, v___x_380_, v___x_379_, v___x_378_, v___x_377_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object* v_____s_383_, uint8_t v_isLower_384_, lean_object* v_as_385_, size_t v_sz_386_, size_t v_i_387_, lean_object* v_b_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = lean_usize_dec_lt(v_i_387_, v_sz_386_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v_b_388_);
return v___x_402_;
}
else
{
lean_object* v_snd_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_465_; 
v_snd_403_ = lean_ctor_get(v_b_388_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_b_388_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_b_388_, 0);
lean_dec(v_unused_466_);
v___x_405_ = v_b_388_;
v_isShared_406_ = v_isSharedCheck_465_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snd_403_);
lean_dec(v_b_388_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_465_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_a_407_; lean_object* v_p_408_; lean_object* v___x_409_; 
v_a_407_ = lean_array_uget_borrowed(v_as_385_, v_i_387_);
v_p_408_ = lean_ctor_get(v_a_407_, 0);
v___x_409_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_408_, v_____s_383_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; lean_object* v_a_412_; lean_object* v___x_441_; uint8_t v___y_443_; 
lean_dec_ref_known(v___x_409_, 1);
v___x_410_ = lean_box(0);
v___x_441_ = lean_box(0);
if (lean_obj_tag(v_p_408_) == 1)
{
lean_object* v_k_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_k_444_ = lean_ctor_get(v_p_408_, 0);
v___x_445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_446_ = lean_int_dec_lt(v_k_444_, v___x_445_);
if (v_isLower_384_ == 0)
{
if (v___x_446_ == 0)
{
v___y_443_ = v___x_401_;
goto v___jp_442_;
}
else
{
goto v___jp_419_;
}
}
else
{
v___y_443_ = v___x_446_;
goto v___jp_442_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_snd_403_);
v___x_447_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_448_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_447_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_dec_ref_known(v___x_448_, 1);
v_a_412_ = v___x_441_;
goto v___jp_411_;
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_del_object(v___x_405_);
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
v___jp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v_a_412_);
lean_ctor_set(v___x_405_, 0, v___x_410_);
v___x_414_ = v___x_405_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_a_412_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
size_t v___x_415_; size_t v___x_416_; 
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_add(v_i_387_, v___x_415_);
v_i_387_ = v___x_416_;
v_b_388_ = v___x_414_;
goto _start;
}
}
v___jp_419_:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_421_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_420_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_432_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_432_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
if (lean_obj_tag(v_a_422_) == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
lean_del_object(v___x_405_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v_a_422_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_snd_403_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_427_);
v___x_429_ = v___x_424_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
lean_object* v_a_431_; 
lean_del_object(v___x_424_);
lean_dec(v_snd_403_);
v_a_431_ = lean_ctor_get(v_a_422_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v_a_422_, 1);
v_a_412_ = v_a_431_;
goto v___jp_411_;
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_del_object(v___x_405_);
lean_dec(v_snd_403_);
v_a_433_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_421_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_421_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
v___jp_442_:
{
if (v___y_443_ == 0)
{
goto v___jp_419_;
}
else
{
lean_dec(v_snd_403_);
v_a_412_ = v___x_441_;
goto v___jp_411_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_del_object(v___x_405_);
lean_dec(v_snd_403_);
v_a_457_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_409_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_409_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_____s_467_ = _args[0];
lean_object* v_isLower_468_ = _args[1];
lean_object* v_as_469_ = _args[2];
lean_object* v_sz_470_ = _args[3];
lean_object* v_i_471_ = _args[4];
lean_object* v_b_472_ = _args[5];
lean_object* v___y_473_ = _args[6];
lean_object* v___y_474_ = _args[7];
lean_object* v___y_475_ = _args[8];
lean_object* v___y_476_ = _args[9];
lean_object* v___y_477_ = _args[10];
lean_object* v___y_478_ = _args[11];
lean_object* v___y_479_ = _args[12];
lean_object* v___y_480_ = _args[13];
lean_object* v___y_481_ = _args[14];
lean_object* v___y_482_ = _args[15];
lean_object* v___y_483_ = _args[16];
lean_object* v___y_484_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_485_; size_t v_sz_boxed_486_; size_t v_i_boxed_487_; lean_object* v_res_488_; 
v_isLower_boxed_485_ = lean_unbox(v_isLower_468_);
v_sz_boxed_486_ = lean_unbox_usize(v_sz_470_);
lean_dec(v_sz_470_);
v_i_boxed_487_ = lean_unbox_usize(v_i_471_);
lean_dec(v_i_471_);
v_res_488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_467_, v_isLower_boxed_485_, v_as_469_, v_sz_boxed_486_, v_i_boxed_487_, v_b_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v_as_469_);
lean_dec(v_____s_467_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object* v_____s_489_, uint8_t v_isLower_490_, lean_object* v_as_491_, size_t v_sz_492_, size_t v_i_493_, lean_object* v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_b_494_);
return v___x_508_;
}
else
{
lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_571_; 
v_snd_509_ = lean_ctor_get(v_b_494_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_b_494_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v_b_494_, 0);
lean_dec(v_unused_572_);
v___x_511_ = v_b_494_;
v_isShared_512_ = v_isSharedCheck_571_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_dec(v_b_494_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_571_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_a_513_; lean_object* v_p_514_; lean_object* v___x_515_; 
v_a_513_ = lean_array_uget_borrowed(v_as_491_, v_i_493_);
v_p_514_ = lean_ctor_get(v_a_513_, 0);
v___x_515_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_514_, v_____s_489_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_a_519_; uint8_t v___y_549_; 
lean_dec_ref_known(v___x_515_, 1);
v___x_516_ = lean_box(0);
v___x_517_ = lean_box(0);
if (lean_obj_tag(v_p_514_) == 1)
{
lean_object* v_k_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_k_550_ = lean_ctor_get(v_p_514_, 0);
v___x_551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_552_ = lean_int_dec_lt(v_k_550_, v___x_551_);
if (v_isLower_490_ == 0)
{
if (v___x_552_ == 0)
{
v___y_549_ = v___x_507_;
goto v___jp_548_;
}
else
{
goto v___jp_526_;
}
}
else
{
v___y_549_ = v___x_552_;
goto v___jp_548_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v_snd_509_);
v___x_553_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_554_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_553_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_dec_ref_known(v___x_554_, 1);
v_a_519_ = v___x_516_;
goto v___jp_518_;
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_del_object(v___x_511_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
v___jp_518_:
{
lean_object* v___x_521_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_a_519_);
lean_ctor_set(v___x_511_, 0, v___x_517_);
v___x_521_ = v___x_511_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_a_519_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_add(v_i_493_, v___x_522_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_489_, v_isLower_490_, v_as_491_, v_sz_492_, v___x_523_, v___x_521_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_524_;
}
}
v___jp_526_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_528_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_527_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_539_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_539_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
if (lean_obj_tag(v_a_529_) == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
lean_del_object(v___x_511_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_a_529_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v_snd_509_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_534_);
v___x_536_ = v___x_531_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
lean_object* v_a_538_; 
lean_del_object(v___x_531_);
lean_dec(v_snd_509_);
v_a_538_ = lean_ctor_get(v_a_529_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v_a_529_, 1);
v_a_519_ = v_a_538_;
goto v___jp_518_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_511_);
lean_dec(v_snd_509_);
v_a_540_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_528_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_528_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
v___jp_548_:
{
if (v___y_549_ == 0)
{
goto v___jp_526_;
}
else
{
lean_dec(v_snd_509_);
v_a_519_ = v___x_516_;
goto v___jp_518_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_511_);
lean_dec(v_snd_509_);
v_a_563_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_515_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_515_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_____s_573_ = _args[0];
lean_object* v_isLower_574_ = _args[1];
lean_object* v_as_575_ = _args[2];
lean_object* v_sz_576_ = _args[3];
lean_object* v_i_577_ = _args[4];
lean_object* v_b_578_ = _args[5];
lean_object* v___y_579_ = _args[6];
lean_object* v___y_580_ = _args[7];
lean_object* v___y_581_ = _args[8];
lean_object* v___y_582_ = _args[9];
lean_object* v___y_583_ = _args[10];
lean_object* v___y_584_ = _args[11];
lean_object* v___y_585_ = _args[12];
lean_object* v___y_586_ = _args[13];
lean_object* v___y_587_ = _args[14];
lean_object* v___y_588_ = _args[15];
lean_object* v___y_589_ = _args[16];
lean_object* v___y_590_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_591_; size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_isLower_boxed_591_ = lean_unbox(v_isLower_574_);
v_sz_boxed_592_ = lean_unbox_usize(v_sz_576_);
lean_dec(v_sz_576_);
v_i_boxed_593_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_573_, v_isLower_boxed_591_, v_as_575_, v_sz_boxed_592_, v_i_boxed_593_, v_b_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v_as_575_);
lean_dec(v_____s_573_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(lean_object* v_init_595_, lean_object* v_____s_596_, uint8_t v_isLower_597_, lean_object* v_n_598_, lean_object* v_b_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
if (lean_obj_tag(v_n_598_) == 0)
{
lean_object* v_cs_612_; lean_object* v___x_613_; lean_object* v___x_614_; size_t v_sz_615_; size_t v___x_616_; lean_object* v___x_617_; 
v_cs_612_ = lean_ctor_get(v_n_598_, 0);
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_b_599_);
v_sz_615_ = lean_array_size(v_cs_612_);
v___x_616_ = ((size_t)0ULL);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_595_, v_____s_596_, v_isLower_597_, v_cs_612_, v_sz_615_, v___x_616_, v___x_614_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_632_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_632_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_fst_622_; 
v_fst_622_ = lean_ctor_get(v_a_618_, 0);
if (lean_obj_tag(v_fst_622_) == 0)
{
lean_object* v_snd_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v_snd_623_ = lean_ctor_get(v_a_618_, 1);
lean_inc(v_snd_623_);
lean_dec(v_a_618_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v_snd_623_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v_val_628_; lean_object* v___x_630_; 
lean_inc_ref(v_fst_622_);
lean_dec(v_a_618_);
v_val_628_ = lean_ctor_get(v_fst_622_, 0);
lean_inc(v_val_628_);
lean_dec_ref_known(v_fst_622_, 1);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_val_628_);
v___x_630_ = v___x_620_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_val_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_a_633_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_617_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_617_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_vs_641_; lean_object* v___x_642_; lean_object* v___x_643_; size_t v_sz_644_; size_t v___x_645_; lean_object* v___x_646_; 
v_vs_641_ = lean_ctor_get(v_n_598_, 0);
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_b_599_);
v_sz_644_ = lean_array_size(v_vs_641_);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_596_, v_isLower_597_, v_vs_641_, v_sz_644_, v___x_645_, v___x_643_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_661_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_661_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_661_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_661_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_fst_651_; 
v_fst_651_ = lean_ctor_get(v_a_647_, 0);
if (lean_obj_tag(v_fst_651_) == 0)
{
lean_object* v_snd_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v_snd_652_ = lean_ctor_get(v_a_647_, 1);
lean_inc(v_snd_652_);
lean_dec(v_a_647_);
v___x_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_653_, 0, v_snd_652_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_653_);
v___x_655_ = v___x_649_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; 
lean_inc_ref(v_fst_651_);
lean_dec(v_a_647_);
v_val_657_ = lean_ctor_get(v_fst_651_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v_fst_651_, 1);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v_val_657_);
v___x_659_ = v___x_649_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_val_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_646_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_646_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_init_670_, lean_object* v_____s_671_, uint8_t v_isLower_672_, lean_object* v_as_673_, size_t v_sz_674_, size_t v_i_675_, lean_object* v_b_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = lean_usize_dec_lt(v_i_675_, v_sz_674_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v_b_676_);
return v___x_690_;
}
else
{
lean_object* v_snd_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_725_; 
v_snd_691_ = lean_ctor_get(v_b_676_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_b_676_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_b_676_, 0);
lean_dec(v_unused_726_);
v___x_693_ = v_b_676_;
v_isShared_694_ = v_isSharedCheck_725_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_691_);
lean_dec(v_b_676_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_725_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_a_695_; lean_object* v___x_696_; 
v_a_695_ = lean_array_uget_borrowed(v_as_673_, v_i_675_);
lean_inc(v_snd_691_);
v___x_696_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_670_, v_____s_671_, v_isLower_672_, v_a_695_, v_snd_691_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_716_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_716_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_716_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_716_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
if (lean_obj_tag(v_a_697_) == 0)
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v_a_697_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_701_);
v___x_703_ = v___x_693_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_snd_691_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_703_);
v___x_705_ = v___x_699_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
lean_del_object(v___x_699_);
lean_dec(v_snd_691_);
v_a_708_ = lean_ctor_get(v_a_697_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v_a_697_, 1);
v___x_709_ = lean_box(0);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v_a_708_);
lean_ctor_set(v___x_693_, 0, v___x_709_);
v___x_711_ = v___x_693_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_a_708_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
size_t v___x_712_; size_t v___x_713_; 
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_add(v_i_675_, v___x_712_);
v_i_675_ = v___x_713_;
v_b_676_ = v___x_711_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_del_object(v___x_693_);
lean_dec(v_snd_691_);
v_a_717_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_696_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_696_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_727_ = _args[0];
lean_object* v_____s_728_ = _args[1];
lean_object* v_isLower_729_ = _args[2];
lean_object* v_as_730_ = _args[3];
lean_object* v_sz_731_ = _args[4];
lean_object* v_i_732_ = _args[5];
lean_object* v_b_733_ = _args[6];
lean_object* v___y_734_ = _args[7];
lean_object* v___y_735_ = _args[8];
lean_object* v___y_736_ = _args[9];
lean_object* v___y_737_ = _args[10];
lean_object* v___y_738_ = _args[11];
lean_object* v___y_739_ = _args[12];
lean_object* v___y_740_ = _args[13];
lean_object* v___y_741_ = _args[14];
lean_object* v___y_742_ = _args[15];
lean_object* v___y_743_ = _args[16];
lean_object* v___y_744_ = _args[17];
lean_object* v___y_745_ = _args[18];
_start:
{
uint8_t v_isLower_boxed_746_; size_t v_sz_boxed_747_; size_t v_i_boxed_748_; lean_object* v_res_749_; 
v_isLower_boxed_746_ = lean_unbox(v_isLower_729_);
v_sz_boxed_747_ = lean_unbox_usize(v_sz_731_);
lean_dec(v_sz_731_);
v_i_boxed_748_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_727_, v_____s_728_, v_isLower_boxed_746_, v_as_730_, v_sz_boxed_747_, v_i_boxed_748_, v_b_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v_as_730_);
lean_dec(v_____s_728_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_init_750_ = _args[0];
lean_object* v_____s_751_ = _args[1];
lean_object* v_isLower_752_ = _args[2];
lean_object* v_n_753_ = _args[3];
lean_object* v_b_754_ = _args[4];
lean_object* v___y_755_ = _args[5];
lean_object* v___y_756_ = _args[6];
lean_object* v___y_757_ = _args[7];
lean_object* v___y_758_ = _args[8];
lean_object* v___y_759_ = _args[9];
lean_object* v___y_760_ = _args[10];
lean_object* v___y_761_ = _args[11];
lean_object* v___y_762_ = _args[12];
lean_object* v___y_763_ = _args[13];
lean_object* v___y_764_ = _args[14];
lean_object* v___y_765_ = _args[15];
lean_object* v___y_766_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_767_; lean_object* v_res_768_; 
v_isLower_boxed_767_ = lean_unbox(v_isLower_752_);
v_res_768_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_750_, v_____s_751_, v_isLower_boxed_767_, v_n_753_, v_b_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v_n_753_);
lean_dec(v_____s_751_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object* v_____s_769_, uint8_t v_isLower_770_, lean_object* v_as_771_, size_t v_sz_772_, size_t v_i_773_, lean_object* v_b_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_lt(v_i_773_, v_sz_772_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_b_774_);
return v___x_788_;
}
else
{
lean_object* v_snd_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_858_; 
v_snd_789_ = lean_ctor_get(v_b_774_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_b_774_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_b_774_, 0);
lean_dec(v_unused_859_);
v___x_791_ = v_b_774_;
v_isShared_792_ = v_isSharedCheck_858_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_789_);
lean_dec(v_b_774_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_858_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_a_793_; lean_object* v_p_794_; lean_object* v___x_795_; 
v_a_793_ = lean_array_uget_borrowed(v_as_771_, v_i_773_);
v_p_794_ = lean_ctor_get(v_a_793_, 0);
v___x_795_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_794_, v_____s_769_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; lean_object* v_a_798_; lean_object* v___x_834_; uint8_t v___y_836_; 
lean_dec_ref_known(v___x_795_, 1);
v___x_796_ = lean_box(0);
v___x_834_ = lean_box(0);
if (lean_obj_tag(v_p_794_) == 1)
{
lean_object* v_k_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_k_837_ = lean_ctor_get(v_p_794_, 0);
v___x_838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_839_ = lean_int_dec_lt(v_k_837_, v___x_838_);
if (v_isLower_770_ == 0)
{
if (v___x_839_ == 0)
{
v___y_836_ = v___x_787_;
goto v___jp_835_;
}
else
{
goto v___jp_805_;
}
}
else
{
v___y_836_ = v___x_839_;
goto v___jp_835_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_snd_789_);
v___x_840_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_841_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_840_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_dec_ref_known(v___x_841_, 1);
v_a_798_ = v___x_834_;
goto v___jp_797_;
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_del_object(v___x_791_);
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
v___jp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v_a_798_);
lean_ctor_set(v___x_791_, 0, v___x_796_);
v___x_800_ = v___x_791_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_a_798_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
size_t v___x_801_; size_t v___x_802_; 
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_773_, v___x_801_);
v_i_773_ = v___x_802_;
v_b_774_ = v___x_800_;
goto _start;
}
}
v___jp_805_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_807_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_806_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_825_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_825_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_825_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_825_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_823_; 
lean_del_object(v___x_791_);
v_a_812_ = lean_ctor_get(v_a_808_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_823_ == 0)
{
v___x_814_ = v_a_808_;
v_isShared_815_ = v_isSharedCheck_823_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v_a_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_823_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 1);
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_822_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_snd_789_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_818_);
v___x_820_ = v___x_810_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_824_; 
lean_del_object(v___x_810_);
lean_dec(v_snd_789_);
v_a_824_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v_a_808_, 1);
v_a_798_ = v_a_824_;
goto v___jp_797_;
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_del_object(v___x_791_);
lean_dec(v_snd_789_);
v_a_826_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_807_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_807_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
v___jp_835_:
{
if (v___y_836_ == 0)
{
goto v___jp_805_;
}
else
{
lean_dec(v_snd_789_);
v_a_798_ = v___x_834_;
goto v___jp_797_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_del_object(v___x_791_);
lean_dec(v_snd_789_);
v_a_850_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_795_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_795_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_____s_860_ = _args[0];
lean_object* v_isLower_861_ = _args[1];
lean_object* v_as_862_ = _args[2];
lean_object* v_sz_863_ = _args[3];
lean_object* v_i_864_ = _args[4];
lean_object* v_b_865_ = _args[5];
lean_object* v___y_866_ = _args[6];
lean_object* v___y_867_ = _args[7];
lean_object* v___y_868_ = _args[8];
lean_object* v___y_869_ = _args[9];
lean_object* v___y_870_ = _args[10];
lean_object* v___y_871_ = _args[11];
lean_object* v___y_872_ = _args[12];
lean_object* v___y_873_ = _args[13];
lean_object* v___y_874_ = _args[14];
lean_object* v___y_875_ = _args[15];
lean_object* v___y_876_ = _args[16];
lean_object* v___y_877_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_878_; size_t v_sz_boxed_879_; size_t v_i_boxed_880_; lean_object* v_res_881_; 
v_isLower_boxed_878_ = lean_unbox(v_isLower_861_);
v_sz_boxed_879_ = lean_unbox_usize(v_sz_863_);
lean_dec(v_sz_863_);
v_i_boxed_880_ = lean_unbox_usize(v_i_864_);
lean_dec(v_i_864_);
v_res_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_860_, v_isLower_boxed_878_, v_as_862_, v_sz_boxed_879_, v_i_boxed_880_, v_b_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v_as_862_);
lean_dec(v_____s_860_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(lean_object* v_____s_882_, uint8_t v_isLower_883_, lean_object* v_as_884_, size_t v_sz_885_, size_t v_i_886_, lean_object* v_b_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = lean_usize_dec_lt(v_i_886_, v_sz_885_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_b_887_);
return v___x_901_;
}
else
{
lean_object* v_snd_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_971_; 
v_snd_902_ = lean_ctor_get(v_b_887_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_b_887_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v_b_887_, 0);
lean_dec(v_unused_972_);
v___x_904_ = v_b_887_;
v_isShared_905_ = v_isSharedCheck_971_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_snd_902_);
lean_dec(v_b_887_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_971_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_a_906_; lean_object* v_p_907_; lean_object* v___x_908_; 
v_a_906_ = lean_array_uget_borrowed(v_as_884_, v_i_886_);
v_p_907_ = lean_ctor_get(v_a_906_, 0);
v___x_908_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_907_, v_____s_882_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_a_912_; uint8_t v___y_949_; 
lean_dec_ref_known(v___x_908_, 1);
v___x_909_ = lean_box(0);
v___x_910_ = lean_box(0);
if (lean_obj_tag(v_p_907_) == 1)
{
lean_object* v_k_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_k_950_ = lean_ctor_get(v_p_907_, 0);
v___x_951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_952_ = lean_int_dec_lt(v_k_950_, v___x_951_);
if (v_isLower_883_ == 0)
{
if (v___x_952_ == 0)
{
v___y_949_ = v___x_900_;
goto v___jp_948_;
}
else
{
goto v___jp_919_;
}
}
else
{
v___y_949_ = v___x_952_;
goto v___jp_948_;
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v_snd_902_);
v___x_953_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_954_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_953_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_dec_ref_known(v___x_954_, 1);
v_a_912_ = v___x_909_;
goto v___jp_911_;
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_904_);
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
v___jp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_a_912_);
lean_ctor_set(v___x_904_, 0, v___x_910_);
v___x_914_ = v___x_904_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_a_912_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_886_, v___x_915_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_882_, v_isLower_883_, v_as_884_, v_sz_885_, v___x_916_, v___x_914_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_917_;
}
}
v___jp_919_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_921_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_920_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_939_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_939_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_939_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_939_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
if (lean_obj_tag(v_a_922_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_937_; 
lean_del_object(v___x_904_);
v_a_926_ = lean_ctor_get(v_a_922_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_922_);
if (v_isSharedCheck_937_ == 0)
{
v___x_928_ = v_a_922_;
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v_a_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 1);
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_936_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v_snd_902_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_932_);
v___x_934_ = v___x_924_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_938_; 
lean_del_object(v___x_924_);
lean_dec(v_snd_902_);
v_a_938_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v_a_922_, 1);
v_a_912_ = v_a_938_;
goto v___jp_911_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_del_object(v___x_904_);
lean_dec(v_snd_902_);
v_a_940_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_921_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_921_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
v___jp_948_:
{
if (v___y_949_ == 0)
{
goto v___jp_919_;
}
else
{
lean_dec(v_snd_902_);
v_a_912_ = v___x_909_;
goto v___jp_911_;
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_del_object(v___x_904_);
lean_dec(v_snd_902_);
v_a_963_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_908_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_908_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_973_ = _args[0];
lean_object* v_isLower_974_ = _args[1];
lean_object* v_as_975_ = _args[2];
lean_object* v_sz_976_ = _args[3];
lean_object* v_i_977_ = _args[4];
lean_object* v_b_978_ = _args[5];
lean_object* v___y_979_ = _args[6];
lean_object* v___y_980_ = _args[7];
lean_object* v___y_981_ = _args[8];
lean_object* v___y_982_ = _args[9];
lean_object* v___y_983_ = _args[10];
lean_object* v___y_984_ = _args[11];
lean_object* v___y_985_ = _args[12];
lean_object* v___y_986_ = _args[13];
lean_object* v___y_987_ = _args[14];
lean_object* v___y_988_ = _args[15];
lean_object* v___y_989_ = _args[16];
lean_object* v___y_990_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_991_; size_t v_sz_boxed_992_; size_t v_i_boxed_993_; lean_object* v_res_994_; 
v_isLower_boxed_991_ = lean_unbox(v_isLower_974_);
v_sz_boxed_992_ = lean_unbox_usize(v_sz_976_);
lean_dec(v_sz_976_);
v_i_boxed_993_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_res_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_973_, v_isLower_boxed_991_, v_as_975_, v_sz_boxed_992_, v_i_boxed_993_, v_b_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v_as_975_);
lean_dec(v_____s_973_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(lean_object* v_____s_995_, uint8_t v_isLower_996_, lean_object* v_t_997_, lean_object* v_init_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_root_1011_; lean_object* v_tail_1012_; lean_object* v___x_1013_; 
v_root_1011_ = lean_ctor_get(v_t_997_, 0);
v_tail_1012_ = lean_ctor_get(v_t_997_, 1);
v___x_1013_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_998_, v_____s_995_, v_isLower_996_, v_root_1011_, v_init_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1050_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1050_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1050_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
if (lean_obj_tag(v_a_1014_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; 
v_a_1018_ = lean_ctor_get(v_a_1014_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v_a_1014_, 1);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v_a_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; size_t v_sz_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
lean_del_object(v___x_1016_);
v_a_1022_ = lean_ctor_get(v_a_1014_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v_a_1014_, 1);
v___x_1023_ = lean_box(0);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_a_1022_);
v_sz_1025_ = lean_array_size(v_tail_1012_);
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_995_, v_isLower_996_, v_tail_1012_, v_sz_1025_, v___x_1026_, v___x_1024_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1041_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_fst_1032_; 
v_fst_1032_ = lean_ctor_get(v_a_1028_, 0);
if (lean_obj_tag(v_fst_1032_) == 0)
{
lean_object* v_snd_1033_; lean_object* v___x_1035_; 
v_snd_1033_ = lean_ctor_get(v_a_1028_, 1);
lean_inc(v_snd_1033_);
lean_dec(v_a_1028_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_snd_1033_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_snd_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
else
{
lean_object* v_val_1037_; lean_object* v___x_1039_; 
lean_inc_ref(v_fst_1032_);
lean_dec(v_a_1028_);
v_val_1037_ = lean_ctor_get(v_fst_1032_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v_fst_1032_, 1);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_val_1037_);
v___x_1039_ = v___x_1030_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_val_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
v_a_1042_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1027_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1027_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_a_1051_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1013_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1013_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1059_, lean_object* v_isLower_1060_, lean_object* v_t_1061_, lean_object* v_init_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v_isLower_boxed_1075_; lean_object* v_res_1076_; 
v_isLower_boxed_1075_ = lean_unbox(v_isLower_1060_);
v_res_1076_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_____s_1059_, v_isLower_boxed_1075_, v_t_1061_, v_init_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v_t_1061_);
lean_dec(v_____s_1059_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1077_, lean_object* v_as_1078_, size_t v_sz_1079_, size_t v_i_1080_, lean_object* v_b_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_usize_dec_lt(v_i_1080_, v_sz_1079_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_b_1081_);
return v___x_1095_;
}
else
{
lean_object* v_snd_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1120_; 
v_snd_1096_ = lean_ctor_get(v_b_1081_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_b_1081_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v_b_1081_, 0);
lean_dec(v_unused_1121_);
v___x_1098_ = v_b_1081_;
v_isShared_1099_ = v_isSharedCheck_1120_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_snd_1096_);
lean_dec(v_b_1081_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1120_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_a_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_a_1100_ = lean_array_uget_borrowed(v_as_1078_, v_i_1080_);
v___x_1101_ = lean_box(0);
v___x_1102_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1096_, v_isLower_1077_, v_a_1100_, v___x_1101_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
lean_dec_ref_known(v___x_1102_, 1);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_snd_1096_, v___x_1104_);
lean_dec(v_snd_1096_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1105_);
lean_ctor_set(v___x_1098_, 0, v___x_1103_);
v___x_1107_ = v___x_1098_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
size_t v___x_1108_; size_t v___x_1109_; 
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_i_1080_, v___x_1108_);
v_i_1080_ = v___x_1109_;
v_b_1081_ = v___x_1107_;
goto _start;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_del_object(v___x_1098_);
lean_dec(v_snd_1096_);
v_a_1112_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1102_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1102_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object** _args){
lean_object* v_isLower_1122_ = _args[0];
lean_object* v_as_1123_ = _args[1];
lean_object* v_sz_1124_ = _args[2];
lean_object* v_i_1125_ = _args[3];
lean_object* v_b_1126_ = _args[4];
lean_object* v___y_1127_ = _args[5];
lean_object* v___y_1128_ = _args[6];
lean_object* v___y_1129_ = _args[7];
lean_object* v___y_1130_ = _args[8];
lean_object* v___y_1131_ = _args[9];
lean_object* v___y_1132_ = _args[10];
lean_object* v___y_1133_ = _args[11];
lean_object* v___y_1134_ = _args[12];
lean_object* v___y_1135_ = _args[13];
lean_object* v___y_1136_ = _args[14];
lean_object* v___y_1137_ = _args[15];
lean_object* v___y_1138_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1139_; size_t v_sz_boxed_1140_; size_t v_i_boxed_1141_; lean_object* v_res_1142_; 
v_isLower_boxed_1139_ = lean_unbox(v_isLower_1122_);
v_sz_boxed_1140_ = lean_unbox_usize(v_sz_1124_);
lean_dec(v_sz_1124_);
v_i_boxed_1141_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_res_1142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1139_, v_as_1123_, v_sz_boxed_1140_, v_i_boxed_1141_, v_b_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v_as_1123_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1143_, lean_object* v_as_1144_, size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_usize_dec_lt(v_i_1146_, v_sz_1145_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_b_1147_);
return v___x_1161_;
}
else
{
lean_object* v_snd_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1186_; 
v_snd_1162_ = lean_ctor_get(v_b_1147_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_b_1147_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; 
v_unused_1187_ = lean_ctor_get(v_b_1147_, 0);
lean_dec(v_unused_1187_);
v___x_1164_ = v_b_1147_;
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_snd_1162_);
lean_dec(v_b_1147_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1166_ = lean_array_uget_borrowed(v_as_1144_, v_i_1146_);
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1162_, v_isLower_1143_, v_a_1166_, v___x_1167_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_dec_ref_known(v___x_1168_, 1);
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_add(v_snd_1162_, v___x_1170_);
lean_dec(v_snd_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1171_);
lean_ctor_set(v___x_1164_, 0, v___x_1169_);
v___x_1173_ = v___x_1164_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1146_, v___x_1174_);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1143_, v_as_1144_, v_sz_1145_, v___x_1175_, v___x_1173_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1176_;
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_del_object(v___x_1164_);
lean_dec(v_snd_1162_);
v_a_1178_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1168_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1168_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object** _args){
lean_object* v_isLower_1188_ = _args[0];
lean_object* v_as_1189_ = _args[1];
lean_object* v_sz_1190_ = _args[2];
lean_object* v_i_1191_ = _args[3];
lean_object* v_b_1192_ = _args[4];
lean_object* v___y_1193_ = _args[5];
lean_object* v___y_1194_ = _args[6];
lean_object* v___y_1195_ = _args[7];
lean_object* v___y_1196_ = _args[8];
lean_object* v___y_1197_ = _args[9];
lean_object* v___y_1198_ = _args[10];
lean_object* v___y_1199_ = _args[11];
lean_object* v___y_1200_ = _args[12];
lean_object* v___y_1201_ = _args[13];
lean_object* v___y_1202_ = _args[14];
lean_object* v___y_1203_ = _args[15];
lean_object* v___y_1204_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1205_; size_t v_sz_boxed_1206_; size_t v_i_boxed_1207_; lean_object* v_res_1208_; 
v_isLower_boxed_1205_ = lean_unbox(v_isLower_1188_);
v_sz_boxed_1206_ = lean_unbox_usize(v_sz_1190_);
lean_dec(v_sz_1190_);
v_i_boxed_1207_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1205_, v_as_1189_, v_sz_boxed_1206_, v_i_boxed_1207_, v_b_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v_as_1189_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(lean_object* v_init_1209_, uint8_t v_isLower_1210_, lean_object* v_n_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
if (lean_obj_tag(v_n_1211_) == 0)
{
lean_object* v_cs_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; size_t v_sz_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v_cs_1225_ = lean_ctor_get(v_n_1211_, 0);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_b_1212_);
v_sz_1228_ = lean_array_size(v_cs_1225_);
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1209_, v_isLower_1210_, v_cs_1225_, v_sz_1228_, v___x_1229_, v___x_1227_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1245_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_fst_1235_; 
v_fst_1235_ = lean_ctor_get(v_a_1231_, 0);
if (lean_obj_tag(v_fst_1235_) == 0)
{
lean_object* v_snd_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v_snd_1236_ = lean_ctor_get(v_a_1231_, 1);
lean_inc(v_snd_1236_);
lean_dec(v_a_1231_);
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_snd_1236_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1237_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
else
{
lean_object* v_val_1241_; lean_object* v___x_1243_; 
lean_inc_ref(v_fst_1235_);
lean_dec(v_a_1231_);
v_val_1241_ = lean_ctor_get(v_fst_1235_, 0);
lean_inc(v_val_1241_);
lean_dec_ref_known(v_fst_1235_, 1);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v_val_1241_);
v___x_1243_ = v___x_1233_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_val_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1230_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1230_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
else
{
lean_object* v_vs_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; size_t v_sz_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v_vs_1254_ = lean_ctor_get(v_n_1211_, 0);
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_b_1212_);
v_sz_1257_ = lean_array_size(v_vs_1254_);
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1210_, v_vs_1254_, v_sz_1257_, v___x_1258_, v___x_1256_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1274_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1274_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1274_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_fst_1264_; 
v_fst_1264_ = lean_ctor_get(v_a_1260_, 0);
if (lean_obj_tag(v_fst_1264_) == 0)
{
lean_object* v_snd_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v_snd_1265_ = lean_ctor_get(v_a_1260_, 1);
lean_inc(v_snd_1265_);
lean_dec(v_a_1260_);
v___x_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1266_, 0, v_snd_1265_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1266_);
v___x_1268_ = v___x_1262_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
else
{
lean_object* v_val_1270_; lean_object* v___x_1272_; 
lean_inc_ref(v_fst_1264_);
lean_dec(v_a_1260_);
v_val_1270_ = lean_ctor_get(v_fst_1264_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v_fst_1264_, 1);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v_val_1270_);
v___x_1272_ = v___x_1262_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_val_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
v_a_1275_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1259_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1259_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object* v_init_1283_, uint8_t v_isLower_1284_, lean_object* v_as_1285_, size_t v_sz_1286_, size_t v_i_1287_, lean_object* v_b_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_lt(v_i_1287_, v_sz_1286_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_b_1288_);
return v___x_1302_;
}
else
{
lean_object* v_snd_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1337_; 
v_snd_1303_ = lean_ctor_get(v_b_1288_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_b_1288_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_b_1288_, 0);
lean_dec(v_unused_1338_);
v___x_1305_ = v_b_1288_;
v_isShared_1306_ = v_isSharedCheck_1337_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snd_1303_);
lean_dec(v_b_1288_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1337_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_a_1307_; lean_object* v___x_1308_; 
v_a_1307_ = lean_array_uget_borrowed(v_as_1285_, v_i_1287_);
lean_inc(v_snd_1303_);
v___x_1308_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_1283_, v_isLower_1284_, v_a_1307_, v_snd_1303_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1328_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1328_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1328_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
if (lean_obj_tag(v_a_1309_) == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1309_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1313_);
v___x_1315_ = v___x_1305_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_snd_1303_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1315_);
v___x_1317_ = v___x_1311_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_del_object(v___x_1311_);
lean_dec(v_snd_1303_);
v_a_1320_ = lean_ctor_get(v_a_1309_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v_a_1309_, 1);
v___x_1321_ = lean_box(0);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 1, v_a_1320_);
lean_ctor_set(v___x_1305_, 0, v___x_1321_);
v___x_1323_ = v___x_1305_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_a_1320_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
size_t v___x_1324_; size_t v___x_1325_; 
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_add(v_i_1287_, v___x_1324_);
v_i_1287_ = v___x_1325_;
v_b_1288_ = v___x_1323_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
v_a_1329_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1308_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1308_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_init_1339_ = _args[0];
lean_object* v_isLower_1340_ = _args[1];
lean_object* v_as_1341_ = _args[2];
lean_object* v_sz_1342_ = _args[3];
lean_object* v_i_1343_ = _args[4];
lean_object* v_b_1344_ = _args[5];
lean_object* v___y_1345_ = _args[6];
lean_object* v___y_1346_ = _args[7];
lean_object* v___y_1347_ = _args[8];
lean_object* v___y_1348_ = _args[9];
lean_object* v___y_1349_ = _args[10];
lean_object* v___y_1350_ = _args[11];
lean_object* v___y_1351_ = _args[12];
lean_object* v___y_1352_ = _args[13];
lean_object* v___y_1353_ = _args[14];
lean_object* v___y_1354_ = _args[15];
lean_object* v___y_1355_ = _args[16];
lean_object* v___y_1356_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_1357_; size_t v_sz_boxed_1358_; size_t v_i_boxed_1359_; lean_object* v_res_1360_; 
v_isLower_boxed_1357_ = lean_unbox(v_isLower_1340_);
v_sz_boxed_1358_ = lean_unbox_usize(v_sz_1342_);
lean_dec(v_sz_1342_);
v_i_boxed_1359_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1339_, v_isLower_boxed_1357_, v_as_1341_, v_sz_boxed_1358_, v_i_boxed_1359_, v_b_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v_as_1341_);
lean_dec(v_init_1339_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_init_1361_, lean_object* v_isLower_1362_, lean_object* v_n_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v_isLower_boxed_1377_; lean_object* v_res_1378_; 
v_isLower_boxed_1377_ = lean_unbox(v_isLower_1362_);
v_res_1378_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_1361_, v_isLower_boxed_1377_, v_n_1363_, v_b_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v_n_1363_);
lean_dec(v_init_1361_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1379_, lean_object* v_as_1380_, size_t v_sz_1381_, size_t v_i_1382_, lean_object* v_b_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_usize_dec_lt(v_i_1382_, v_sz_1381_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_b_1383_);
return v___x_1397_;
}
else
{
lean_object* v_snd_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1422_; 
v_snd_1398_ = lean_ctor_get(v_b_1383_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_b_1383_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v_b_1383_, 0);
lean_dec(v_unused_1423_);
v___x_1400_ = v_b_1383_;
v_isShared_1401_ = v_isSharedCheck_1422_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snd_1398_);
lean_dec(v_b_1383_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1422_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_a_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_a_1402_ = lean_array_uget_borrowed(v_as_1380_, v_i_1382_);
v___x_1403_ = lean_box(0);
v___x_1404_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1398_, v_isLower_1379_, v_a_1402_, v___x_1403_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec_ref_known(v___x_1404_, 1);
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_unsigned_to_nat(1u);
v___x_1407_ = lean_nat_add(v_snd_1398_, v___x_1406_);
lean_dec(v_snd_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1407_);
lean_ctor_set(v___x_1400_, 0, v___x_1405_);
v___x_1409_ = v___x_1400_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
size_t v___x_1410_; size_t v___x_1411_; 
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_add(v_i_1382_, v___x_1410_);
v_i_1382_ = v___x_1411_;
v_b_1383_ = v___x_1409_;
goto _start;
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_del_object(v___x_1400_);
lean_dec(v_snd_1398_);
v_a_1414_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1404_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1404_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object** _args){
lean_object* v_isLower_1424_ = _args[0];
lean_object* v_as_1425_ = _args[1];
lean_object* v_sz_1426_ = _args[2];
lean_object* v_i_1427_ = _args[3];
lean_object* v_b_1428_ = _args[4];
lean_object* v___y_1429_ = _args[5];
lean_object* v___y_1430_ = _args[6];
lean_object* v___y_1431_ = _args[7];
lean_object* v___y_1432_ = _args[8];
lean_object* v___y_1433_ = _args[9];
lean_object* v___y_1434_ = _args[10];
lean_object* v___y_1435_ = _args[11];
lean_object* v___y_1436_ = _args[12];
lean_object* v___y_1437_ = _args[13];
lean_object* v___y_1438_ = _args[14];
lean_object* v___y_1439_ = _args[15];
lean_object* v___y_1440_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1441_; size_t v_sz_boxed_1442_; size_t v_i_boxed_1443_; lean_object* v_res_1444_; 
v_isLower_boxed_1441_ = lean_unbox(v_isLower_1424_);
v_sz_boxed_1442_ = lean_unbox_usize(v_sz_1426_);
lean_dec(v_sz_1426_);
v_i_boxed_1443_ = lean_unbox_usize(v_i_1427_);
lean_dec(v_i_1427_);
v_res_1444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_1441_, v_as_1425_, v_sz_boxed_1442_, v_i_boxed_1443_, v_b_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v_as_1425_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1445_, lean_object* v_as_1446_, size_t v_sz_1447_, size_t v_i_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_lt(v_i_1448_, v_sz_1447_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1449_);
return v___x_1463_;
}
else
{
lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1488_; 
v_snd_1464_ = lean_ctor_get(v_b_1449_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_b_1449_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_b_1449_, 0);
lean_dec(v_unused_1489_);
v___x_1466_ = v_b_1449_;
v_isShared_1467_ = v_isSharedCheck_1488_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_dec(v_b_1449_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1488_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_a_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_a_1468_ = lean_array_uget_borrowed(v_as_1446_, v_i_1448_);
v___x_1469_ = lean_box(0);
v___x_1470_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1464_, v_isLower_1445_, v_a_1468_, v___x_1469_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
lean_dec_ref_known(v___x_1470_, 1);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_add(v_snd_1464_, v___x_1472_);
lean_dec(v_snd_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___x_1473_);
lean_ctor_set(v___x_1466_, 0, v___x_1471_);
v___x_1475_ = v___x_1466_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
size_t v___x_1476_; size_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_add(v_i_1448_, v___x_1476_);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1445_, v_as_1446_, v_sz_1447_, v___x_1477_, v___x_1475_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1478_;
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
v_a_1480_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1470_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1470_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_isLower_1490_ = _args[0];
lean_object* v_as_1491_ = _args[1];
lean_object* v_sz_1492_ = _args[2];
lean_object* v_i_1493_ = _args[3];
lean_object* v_b_1494_ = _args[4];
lean_object* v___y_1495_ = _args[5];
lean_object* v___y_1496_ = _args[6];
lean_object* v___y_1497_ = _args[7];
lean_object* v___y_1498_ = _args[8];
lean_object* v___y_1499_ = _args[9];
lean_object* v___y_1500_ = _args[10];
lean_object* v___y_1501_ = _args[11];
lean_object* v___y_1502_ = _args[12];
lean_object* v___y_1503_ = _args[13];
lean_object* v___y_1504_ = _args[14];
lean_object* v___y_1505_ = _args[15];
lean_object* v___y_1506_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1507_; size_t v_sz_boxed_1508_; size_t v_i_boxed_1509_; lean_object* v_res_1510_; 
v_isLower_boxed_1507_ = lean_unbox(v_isLower_1490_);
v_sz_boxed_1508_ = lean_unbox_usize(v_sz_1492_);
lean_dec(v_sz_1492_);
v_i_boxed_1509_ = lean_unbox_usize(v_i_1493_);
lean_dec(v_i_1493_);
v_res_1510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1507_, v_as_1491_, v_sz_boxed_1508_, v_i_boxed_1509_, v_b_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v_as_1491_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(uint8_t v_isLower_1511_, lean_object* v_t_1512_, lean_object* v_init_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_root_1526_; lean_object* v_tail_1527_; lean_object* v___x_1528_; 
v_root_1526_ = lean_ctor_get(v_t_1512_, 0);
v_tail_1527_ = lean_ctor_get(v_t_1512_, 1);
lean_inc(v_init_1513_);
v___x_1528_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_1513_, v_isLower_1511_, v_root_1526_, v_init_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v_init_1513_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1565_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1565_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1565_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
if (lean_obj_tag(v_a_1529_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; 
v_a_1533_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v_a_1529_, 1);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v_a_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; size_t v_sz_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
lean_del_object(v___x_1531_);
v_a_1537_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v_a_1529_, 1);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v_a_1537_);
v_sz_1540_ = lean_array_size(v_tail_1527_);
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_1511_, v_tail_1527_, v_sz_1540_, v___x_1541_, v___x_1539_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1556_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1556_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1556_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_fst_1547_; 
v_fst_1547_ = lean_ctor_get(v_a_1543_, 0);
if (lean_obj_tag(v_fst_1547_) == 0)
{
lean_object* v_snd_1548_; lean_object* v___x_1550_; 
v_snd_1548_ = lean_ctor_get(v_a_1543_, 1);
lean_inc(v_snd_1548_);
lean_dec(v_a_1543_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v_snd_1548_);
v___x_1550_ = v___x_1545_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_snd_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
else
{
lean_object* v_val_1552_; lean_object* v___x_1554_; 
lean_inc_ref(v_fst_1547_);
lean_dec(v_a_1543_);
v_val_1552_ = lean_ctor_get(v_fst_1547_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v_fst_1547_, 1);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v_val_1552_);
v___x_1554_ = v___x_1545_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_val_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
v_a_1557_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1542_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1542_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_a_1566_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1528_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1528_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1574_, lean_object* v_t_1575_, lean_object* v_init_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v_isLower_boxed_1589_; lean_object* v_res_1590_; 
v_isLower_boxed_1589_ = lean_unbox(v_isLower_1574_);
v_res_1590_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_boxed_1589_, v_t_1575_, v_init_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v_t_1575_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(lean_object* v_css_1591_, uint8_t v_isLower_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_x_1605_; lean_object* v___x_1606_; 
v_x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_1592_, v_css_1591_, v_x_1605_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1614_; 
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v___x_1606_, 0);
lean_dec(v_unused_1615_);
v___x_1608_ = v___x_1606_;
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = lean_box(0);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1610_);
v___x_1612_ = v___x_1608_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1606_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1606_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs___boxed(lean_object* v_css_1624_, lean_object* v_isLower_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
uint8_t v_isLower_boxed_1638_; lean_object* v_res_1639_; 
v_isLower_boxed_1638_ = lean_unbox(v_isLower_1625_);
v_res_1639_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_css_1624_, v_isLower_boxed_1638_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_css_1624_);
return v_res_1639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1));
v___x_1643_ = lean_unsigned_to_nat(2u);
v___x_1644_ = lean_unsigned_to_nat(63u);
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0));
v___x_1646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_1647_ = l_mkPanicMessageWithDecl(v___x_1646_, v___x_1645_, v___x_1644_, v___x_1643_, v___x_1642_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v_lowers_1662_; lean_object* v_vars_1663_; lean_object* v_size_1664_; lean_object* v_size_1665_; uint8_t v___x_1666_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v_lowers_1662_ = lean_ctor_get(v_a_1661_, 32);
lean_inc_ref(v_lowers_1662_);
v_vars_1663_ = lean_ctor_get(v_a_1661_, 30);
lean_inc_ref(v_vars_1663_);
lean_dec(v_a_1661_);
v_size_1664_ = lean_ctor_get(v_lowers_1662_, 2);
v_size_1665_ = lean_ctor_get(v_vars_1663_, 2);
lean_inc(v_size_1665_);
lean_dec_ref(v_vars_1663_);
v___x_1666_ = lean_nat_dec_eq(v_size_1664_, v_size_1665_);
lean_dec(v_size_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref(v_lowers_1662_);
v___x_1667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2);
v___x_1668_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_1667_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_lowers_1662_, v___x_1666_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec_ref(v_lowers_1662_);
return v___x_1669_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1660_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1660_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___boxed(lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec(v_a_1678_);
return v_res_1690_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1));
v___x_1694_ = lean_unsigned_to_nat(2u);
v___x_1695_ = lean_unsigned_to_nat(68u);
v___x_1696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0));
v___x_1697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_1698_ = l_mkPanicMessageWithDecl(v___x_1697_, v___x_1696_, v___x_1695_, v___x_1694_, v___x_1693_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v_uppers_1713_; lean_object* v_vars_1714_; lean_object* v_size_1715_; lean_object* v_size_1716_; uint8_t v___x_1717_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v_uppers_1713_ = lean_ctor_get(v_a_1712_, 33);
lean_inc_ref(v_uppers_1713_);
v_vars_1714_ = lean_ctor_get(v_a_1712_, 30);
lean_inc_ref(v_vars_1714_);
lean_dec(v_a_1712_);
v_size_1715_ = lean_ctor_get(v_uppers_1713_, 2);
v_size_1716_ = lean_ctor_get(v_vars_1714_, 2);
lean_inc(v_size_1716_);
lean_dec_ref(v_vars_1714_);
v___x_1717_ = lean_nat_dec_eq(v_size_1715_, v_size_1716_);
lean_dec(v_size_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref(v_uppers_1713_);
v___x_1718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2);
v___x_1719_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_1718_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = 0;
v___x_1721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_uppers_1713_, v___x_1720_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec_ref(v_uppers_1713_);
return v___x_1721_;
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1722_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1711_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1711_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___boxed(lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec(v_a_1730_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_1746_, lean_object* v_as_1747_, size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
uint8_t v___x_1763_; 
v___x_1763_ = lean_usize_dec_lt(v_i_1749_, v_sz_1748_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_b_1750_);
return v___x_1764_;
}
else
{
lean_object* v_a_1765_; lean_object* v_p_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v_b_1750_);
v_a_1765_ = lean_array_uget_borrowed(v_as_1747_, v_i_1749_);
v_p_1766_ = lean_ctor_get(v_a_1765_, 0);
v___x_1767_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_1766_, v_____s_1746_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; 
lean_dec_ref_known(v___x_1767_, 1);
v___x_1768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_add(v_i_1749_, v___x_1769_);
v_i_1749_ = v___x_1770_;
v_b_1750_ = v___x_1768_;
goto _start;
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_a_1772_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1767_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1767_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_____s_1780_ = _args[0];
lean_object* v_as_1781_ = _args[1];
lean_object* v_sz_1782_ = _args[2];
lean_object* v_i_1783_ = _args[3];
lean_object* v_b_1784_ = _args[4];
lean_object* v___y_1785_ = _args[5];
lean_object* v___y_1786_ = _args[6];
lean_object* v___y_1787_ = _args[7];
lean_object* v___y_1788_ = _args[8];
lean_object* v___y_1789_ = _args[9];
lean_object* v___y_1790_ = _args[10];
lean_object* v___y_1791_ = _args[11];
lean_object* v___y_1792_ = _args[12];
lean_object* v___y_1793_ = _args[13];
lean_object* v___y_1794_ = _args[14];
lean_object* v___y_1795_ = _args[15];
lean_object* v___y_1796_ = _args[16];
_start:
{
size_t v_sz_boxed_1797_; size_t v_i_boxed_1798_; lean_object* v_res_1799_; 
v_sz_boxed_1797_ = lean_unbox_usize(v_sz_1782_);
lean_dec(v_sz_1782_);
v_i_boxed_1798_ = lean_unbox_usize(v_i_1783_);
lean_dec(v_i_1783_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_1780_, v_as_1781_, v_sz_boxed_1797_, v_i_boxed_1798_, v_b_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v_as_1781_);
lean_dec(v_____s_1780_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_1800_, lean_object* v_as_1801_, size_t v_sz_1802_, size_t v_i_1803_, lean_object* v_b_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_usize_dec_lt(v_i_1803_, v_sz_1802_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_b_1804_);
return v___x_1818_;
}
else
{
lean_object* v_a_1819_; lean_object* v_p_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v_b_1804_);
v_a_1819_ = lean_array_uget_borrowed(v_as_1801_, v_i_1803_);
v_p_1820_ = lean_ctor_get(v_a_1819_, 0);
v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_1820_, v_____s_1800_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
lean_dec_ref_known(v___x_1821_, 1);
v___x_1822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_1823_ = ((size_t)1ULL);
v___x_1824_ = lean_usize_add(v_i_1803_, v___x_1823_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_1800_, v_as_1801_, v_sz_1802_, v___x_1824_, v___x_1822_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
return v___x_1825_;
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_a_1826_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1821_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1821_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_____s_1834_ = _args[0];
lean_object* v_as_1835_ = _args[1];
lean_object* v_sz_1836_ = _args[2];
lean_object* v_i_1837_ = _args[3];
lean_object* v_b_1838_ = _args[4];
lean_object* v___y_1839_ = _args[5];
lean_object* v___y_1840_ = _args[6];
lean_object* v___y_1841_ = _args[7];
lean_object* v___y_1842_ = _args[8];
lean_object* v___y_1843_ = _args[9];
lean_object* v___y_1844_ = _args[10];
lean_object* v___y_1845_ = _args[11];
lean_object* v___y_1846_ = _args[12];
lean_object* v___y_1847_ = _args[13];
lean_object* v___y_1848_ = _args[14];
lean_object* v___y_1849_ = _args[15];
lean_object* v___y_1850_ = _args[16];
_start:
{
size_t v_sz_boxed_1851_; size_t v_i_boxed_1852_; lean_object* v_res_1853_; 
v_sz_boxed_1851_ = lean_unbox_usize(v_sz_1836_);
lean_dec(v_sz_1836_);
v_i_boxed_1852_ = lean_unbox_usize(v_i_1837_);
lean_dec(v_i_1837_);
v_res_1853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_1834_, v_as_1835_, v_sz_boxed_1851_, v_i_boxed_1852_, v_b_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v_as_1835_);
lean_dec(v_____s_1834_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_init_1854_, lean_object* v_____s_1855_, lean_object* v_n_1856_, lean_object* v_b_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
if (lean_obj_tag(v_n_1856_) == 0)
{
lean_object* v_cs_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; size_t v_sz_1873_; size_t v___x_1874_; lean_object* v___x_1875_; 
v_cs_1870_ = lean_ctor_get(v_n_1856_, 0);
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_b_1857_);
v_sz_1873_ = lean_array_size(v_cs_1870_);
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_1854_, v_____s_1855_, v_cs_1870_, v_sz_1873_, v___x_1874_, v___x_1872_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1890_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1890_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1890_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_fst_1880_; 
v_fst_1880_ = lean_ctor_get(v_a_1876_, 0);
if (lean_obj_tag(v_fst_1880_) == 0)
{
lean_object* v_snd_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v_snd_1881_ = lean_ctor_get(v_a_1876_, 1);
lean_inc(v_snd_1881_);
lean_dec(v_a_1876_);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_snd_1881_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1882_);
v___x_1884_ = v___x_1878_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
else
{
lean_object* v_val_1886_; lean_object* v___x_1888_; 
lean_inc_ref(v_fst_1880_);
lean_dec(v_a_1876_);
v_val_1886_ = lean_ctor_get(v_fst_1880_, 0);
lean_inc(v_val_1886_);
lean_dec_ref_known(v_fst_1880_, 1);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v_val_1886_);
v___x_1888_ = v___x_1878_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_val_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1875_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1875_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_vs_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; size_t v_sz_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v_vs_1899_ = lean_ctor_get(v_n_1856_, 0);
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_b_1857_);
v_sz_1902_ = lean_array_size(v_vs_1899_);
v___x_1903_ = ((size_t)0ULL);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_1855_, v_vs_1899_, v_sz_1902_, v___x_1903_, v___x_1901_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1919_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1919_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1919_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_fst_1909_; 
v_fst_1909_ = lean_ctor_get(v_a_1905_, 0);
if (lean_obj_tag(v_fst_1909_) == 0)
{
lean_object* v_snd_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v_snd_1910_ = lean_ctor_get(v_a_1905_, 1);
lean_inc(v_snd_1910_);
lean_dec(v_a_1905_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_snd_1910_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1911_);
v___x_1913_ = v___x_1907_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
else
{
lean_object* v_val_1915_; lean_object* v___x_1917_; 
lean_inc_ref(v_fst_1909_);
lean_dec(v_a_1905_);
v_val_1915_ = lean_ctor_get(v_fst_1909_, 0);
lean_inc(v_val_1915_);
lean_dec_ref_known(v_fst_1909_, 1);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v_val_1915_);
v___x_1917_ = v___x_1907_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_val_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1904_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1904_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_1928_, lean_object* v_____s_1929_, lean_object* v_as_1930_, size_t v_sz_1931_, size_t v_i_1932_, lean_object* v_b_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_usize_dec_lt(v_i_1932_, v_sz_1931_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_b_1933_);
return v___x_1947_;
}
else
{
lean_object* v_snd_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1982_; 
v_snd_1948_ = lean_ctor_get(v_b_1933_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_b_1933_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_b_1933_, 0);
lean_dec(v_unused_1983_);
v___x_1950_ = v_b_1933_;
v_isShared_1951_ = v_isSharedCheck_1982_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1948_);
lean_dec(v_b_1933_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1982_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_array_uget_borrowed(v_as_1930_, v_i_1932_);
lean_inc(v_snd_1948_);
v___x_1953_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_1928_, v_____s_1929_, v_a_1952_, v_snd_1948_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1973_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1973_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1973_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
if (lean_obj_tag(v_a_1954_) == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1954_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1958_);
v___x_1960_ = v___x_1950_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_snd_1948_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1960_);
v___x_1962_ = v___x_1956_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
lean_del_object(v___x_1956_);
lean_dec(v_snd_1948_);
v_a_1965_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v_a_1954_, 1);
v___x_1966_ = lean_box(0);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v_a_1965_);
lean_ctor_set(v___x_1950_, 0, v___x_1966_);
v___x_1968_ = v___x_1950_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_a_1965_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
size_t v___x_1969_; size_t v___x_1970_; 
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1932_, v___x_1969_);
v_i_1932_ = v___x_1970_;
v_b_1933_ = v___x_1968_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_del_object(v___x_1950_);
lean_dec(v_snd_1948_);
v_a_1974_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1953_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1953_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1984_ = _args[0];
lean_object* v_____s_1985_ = _args[1];
lean_object* v_as_1986_ = _args[2];
lean_object* v_sz_1987_ = _args[3];
lean_object* v_i_1988_ = _args[4];
lean_object* v_b_1989_ = _args[5];
lean_object* v___y_1990_ = _args[6];
lean_object* v___y_1991_ = _args[7];
lean_object* v___y_1992_ = _args[8];
lean_object* v___y_1993_ = _args[9];
lean_object* v___y_1994_ = _args[10];
lean_object* v___y_1995_ = _args[11];
lean_object* v___y_1996_ = _args[12];
lean_object* v___y_1997_ = _args[13];
lean_object* v___y_1998_ = _args[14];
lean_object* v___y_1999_ = _args[15];
lean_object* v___y_2000_ = _args[16];
lean_object* v___y_2001_ = _args[17];
_start:
{
size_t v_sz_boxed_2002_; size_t v_i_boxed_2003_; lean_object* v_res_2004_; 
v_sz_boxed_2002_ = lean_unbox_usize(v_sz_1987_);
lean_dec(v_sz_1987_);
v_i_boxed_2003_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_1984_, v_____s_1985_, v_as_1986_, v_sz_boxed_2002_, v_i_boxed_2003_, v_b_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v_as_1986_);
lean_dec(v_____s_1985_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_init_2005_, lean_object* v_____s_2006_, lean_object* v_n_2007_, lean_object* v_b_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_2005_, v_____s_2006_, v_n_2007_, v_b_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v_n_2007_);
lean_dec(v_____s_2006_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_2025_, lean_object* v_as_2026_, size_t v_sz_2027_, size_t v_i_2028_, lean_object* v_b_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v___x_2042_; 
v___x_2042_ = lean_usize_dec_lt(v_i_2028_, v_sz_2027_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_b_2029_);
return v___x_2043_;
}
else
{
lean_object* v_a_2044_; lean_object* v_p_2045_; lean_object* v___x_2046_; 
lean_dec_ref(v_b_2029_);
v_a_2044_ = lean_array_uget_borrowed(v_as_2026_, v_i_2028_);
v_p_2045_ = lean_ctor_get(v_a_2044_, 0);
v___x_2046_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_2045_, v_____s_2025_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; 
lean_dec_ref_known(v___x_2046_, 1);
v___x_2047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2028_, v___x_2048_);
v_i_2028_ = v___x_2049_;
v_b_2029_ = v___x_2047_;
goto _start;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2046_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2046_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_____s_2059_ = _args[0];
lean_object* v_as_2060_ = _args[1];
lean_object* v_sz_2061_ = _args[2];
lean_object* v_i_2062_ = _args[3];
lean_object* v_b_2063_ = _args[4];
lean_object* v___y_2064_ = _args[5];
lean_object* v___y_2065_ = _args[6];
lean_object* v___y_2066_ = _args[7];
lean_object* v___y_2067_ = _args[8];
lean_object* v___y_2068_ = _args[9];
lean_object* v___y_2069_ = _args[10];
lean_object* v___y_2070_ = _args[11];
lean_object* v___y_2071_ = _args[12];
lean_object* v___y_2072_ = _args[13];
lean_object* v___y_2073_ = _args[14];
lean_object* v___y_2074_ = _args[15];
lean_object* v___y_2075_ = _args[16];
_start:
{
size_t v_sz_boxed_2076_; size_t v_i_boxed_2077_; lean_object* v_res_2078_; 
v_sz_boxed_2076_ = lean_unbox_usize(v_sz_2061_);
lean_dec(v_sz_2061_);
v_i_boxed_2077_ = lean_unbox_usize(v_i_2062_);
lean_dec(v_i_2062_);
v_res_2078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_2059_, v_as_2060_, v_sz_boxed_2076_, v_i_boxed_2077_, v_b_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v_as_2060_);
lean_dec(v_____s_2059_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_2079_, lean_object* v_as_2080_, size_t v_sz_2081_, size_t v_i_2082_, lean_object* v_b_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_lt(v_i_2082_, v_sz_2081_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_b_2083_);
return v___x_2097_;
}
else
{
lean_object* v_a_2098_; lean_object* v_p_2099_; lean_object* v___x_2100_; 
lean_dec_ref(v_b_2083_);
v_a_2098_ = lean_array_uget_borrowed(v_as_2080_, v_i_2082_);
v_p_2099_ = lean_ctor_get(v_a_2098_, 0);
v___x_2100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_2099_, v_____s_2079_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; 
lean_dec_ref_known(v___x_2100_, 1);
v___x_2101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_i_2082_, v___x_2102_);
v___x_2104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_2079_, v_as_2080_, v_sz_2081_, v___x_2103_, v___x_2101_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
return v___x_2104_;
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2100_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2100_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_____s_2113_ = _args[0];
lean_object* v_as_2114_ = _args[1];
lean_object* v_sz_2115_ = _args[2];
lean_object* v_i_2116_ = _args[3];
lean_object* v_b_2117_ = _args[4];
lean_object* v___y_2118_ = _args[5];
lean_object* v___y_2119_ = _args[6];
lean_object* v___y_2120_ = _args[7];
lean_object* v___y_2121_ = _args[8];
lean_object* v___y_2122_ = _args[9];
lean_object* v___y_2123_ = _args[10];
lean_object* v___y_2124_ = _args[11];
lean_object* v___y_2125_ = _args[12];
lean_object* v___y_2126_ = _args[13];
lean_object* v___y_2127_ = _args[14];
lean_object* v___y_2128_ = _args[15];
lean_object* v___y_2129_ = _args[16];
_start:
{
size_t v_sz_boxed_2130_; size_t v_i_boxed_2131_; lean_object* v_res_2132_; 
v_sz_boxed_2130_ = lean_unbox_usize(v_sz_2115_);
lean_dec(v_sz_2115_);
v_i_boxed_2131_ = lean_unbox_usize(v_i_2116_);
lean_dec(v_i_2116_);
v_res_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_2113_, v_as_2114_, v_sz_boxed_2130_, v_i_boxed_2131_, v_b_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v_as_2114_);
lean_dec(v_____s_2113_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(lean_object* v_____s_2133_, lean_object* v_t_2134_, lean_object* v_init_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_root_2148_; lean_object* v_tail_2149_; lean_object* v___x_2150_; 
v_root_2148_ = lean_ctor_get(v_t_2134_, 0);
v_tail_2149_ = lean_ctor_get(v_t_2134_, 1);
v___x_2150_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_2135_, v_____s_2133_, v_root_2148_, v_init_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2187_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2187_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2187_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
if (lean_obj_tag(v_a_2151_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; 
v_a_2155_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v_a_2151_, 1);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v_a_2155_);
v___x_2157_ = v___x_2153_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; size_t v_sz_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
lean_del_object(v___x_2153_);
v_a_2159_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v_a_2151_, 1);
v___x_2160_ = lean_box(0);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_a_2159_);
v_sz_2162_ = lean_array_size(v_tail_2149_);
v___x_2163_ = ((size_t)0ULL);
v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_2133_, v_tail_2149_, v_sz_2162_, v___x_2163_, v___x_2161_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2178_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2178_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2178_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v_fst_2169_; 
v_fst_2169_ = lean_ctor_get(v_a_2165_, 0);
if (lean_obj_tag(v_fst_2169_) == 0)
{
lean_object* v_snd_2170_; lean_object* v___x_2172_; 
v_snd_2170_ = lean_ctor_get(v_a_2165_, 1);
lean_inc(v_snd_2170_);
lean_dec(v_a_2165_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v_snd_2170_);
v___x_2172_ = v___x_2167_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_snd_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
else
{
lean_object* v_val_2174_; lean_object* v___x_2176_; 
lean_inc_ref(v_fst_2169_);
lean_dec(v_a_2165_);
v_val_2174_ = lean_ctor_get(v_fst_2169_, 0);
lean_inc(v_val_2174_);
lean_dec_ref_known(v_fst_2169_, 1);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v_val_2174_);
v___x_2176_ = v___x_2167_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_val_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
v_a_2179_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2164_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2164_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_a_2188_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2150_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2150_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_2196_, lean_object* v_t_2197_, lean_object* v_init_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_____s_2196_, v_t_2197_, v_init_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v_t_2197_);
lean_dec(v_____s_2196_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_2212_, size_t v_sz_2213_, size_t v_i_2214_, lean_object* v_b_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_usize_dec_lt(v_i_2214_, v_sz_2213_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_b_2215_);
return v___x_2229_;
}
else
{
lean_object* v_snd_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2254_; 
v_snd_2230_ = lean_ctor_get(v_b_2215_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_b_2215_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v_b_2215_, 0);
lean_dec(v_unused_2255_);
v___x_2232_ = v_b_2215_;
v_isShared_2233_ = v_isSharedCheck_2254_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_snd_2230_);
lean_dec(v_b_2215_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2254_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_a_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_a_2234_ = lean_array_uget_borrowed(v_as_2212_, v_i_2214_);
v___x_2235_ = lean_box(0);
v___x_2236_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2230_, v_a_2234_, v___x_2235_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec_ref_known(v___x_2236_, 1);
v___x_2237_ = lean_box(0);
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_add(v_snd_2230_, v___x_2238_);
lean_dec(v_snd_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v___x_2239_);
lean_ctor_set(v___x_2232_, 0, v___x_2237_);
v___x_2241_ = v___x_2232_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
size_t v___x_2242_; size_t v___x_2243_; 
v___x_2242_ = ((size_t)1ULL);
v___x_2243_ = lean_usize_add(v_i_2214_, v___x_2242_);
v_i_2214_ = v___x_2243_;
v_b_2215_ = v___x_2241_;
goto _start;
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_del_object(v___x_2232_);
lean_dec(v_snd_2230_);
v_a_2246_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2236_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2236_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_2256_, lean_object* v_sz_2257_, lean_object* v_i_2258_, lean_object* v_b_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
size_t v_sz_boxed_2272_; size_t v_i_boxed_2273_; lean_object* v_res_2274_; 
v_sz_boxed_2272_ = lean_unbox_usize(v_sz_2257_);
lean_dec(v_sz_2257_);
v_i_boxed_2273_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_res_2274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_2256_, v_sz_boxed_2272_, v_i_boxed_2273_, v_b_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v_as_2256_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_2275_, size_t v_sz_2276_, size_t v_i_2277_, lean_object* v_b_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_usize_dec_lt(v_i_2277_, v_sz_2276_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_b_2278_);
return v___x_2292_;
}
else
{
lean_object* v_snd_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2317_; 
v_snd_2293_ = lean_ctor_get(v_b_2278_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_b_2278_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v_b_2278_, 0);
lean_dec(v_unused_2318_);
v___x_2295_ = v_b_2278_;
v_isShared_2296_ = v_isSharedCheck_2317_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_snd_2293_);
lean_dec(v_b_2278_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2317_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_a_2297_ = lean_array_uget_borrowed(v_as_2275_, v_i_2277_);
v___x_2298_ = lean_box(0);
v___x_2299_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2293_, v_a_2297_, v___x_2298_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
lean_dec_ref_known(v___x_2299_, 1);
v___x_2300_ = lean_box(0);
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_nat_add(v_snd_2293_, v___x_2301_);
lean_dec(v_snd_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 1, v___x_2302_);
lean_ctor_set(v___x_2295_, 0, v___x_2300_);
v___x_2304_ = v___x_2295_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_add(v_i_2277_, v___x_2305_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_2275_, v_sz_2276_, v___x_2306_, v___x_2304_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2307_;
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_del_object(v___x_2295_);
lean_dec(v_snd_2293_);
v_a_2309_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2299_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2299_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_2319_, lean_object* v_sz_2320_, lean_object* v_i_2321_, lean_object* v_b_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
size_t v_sz_boxed_2335_; size_t v_i_boxed_2336_; lean_object* v_res_2337_; 
v_sz_boxed_2335_ = lean_unbox_usize(v_sz_2320_);
lean_dec(v_sz_2320_);
v_i_boxed_2336_ = lean_unbox_usize(v_i_2321_);
lean_dec(v_i_2321_);
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_as_2319_, v_sz_boxed_2335_, v_i_boxed_2336_, v_b_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v_as_2319_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_2338_, size_t v_sz_2339_, size_t v_i_2340_, lean_object* v_b_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_usize_dec_lt(v_i_2340_, v_sz_2339_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_b_2341_);
return v___x_2355_;
}
else
{
lean_object* v_snd_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2380_; 
v_snd_2356_ = lean_ctor_get(v_b_2341_, 1);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_b_2341_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v_b_2341_, 0);
lean_dec(v_unused_2381_);
v___x_2358_ = v_b_2341_;
v_isShared_2359_ = v_isSharedCheck_2380_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_snd_2356_);
lean_dec(v_b_2341_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2380_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_a_2360_ = lean_array_uget_borrowed(v_as_2338_, v_i_2340_);
v___x_2361_ = lean_box(0);
v___x_2362_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2356_, v_a_2360_, v___x_2361_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
lean_dec_ref_known(v___x_2362_, 1);
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_add(v_snd_2356_, v___x_2364_);
lean_dec(v_snd_2356_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 1, v___x_2365_);
lean_ctor_set(v___x_2358_, 0, v___x_2363_);
v___x_2367_ = v___x_2358_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
size_t v___x_2368_; size_t v___x_2369_; 
v___x_2368_ = ((size_t)1ULL);
v___x_2369_ = lean_usize_add(v_i_2340_, v___x_2368_);
v_i_2340_ = v___x_2369_;
v_b_2341_ = v___x_2367_;
goto _start;
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_del_object(v___x_2358_);
lean_dec(v_snd_2356_);
v_a_2372_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2362_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2362_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_2382_, lean_object* v_sz_2383_, lean_object* v_i_2384_, lean_object* v_b_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
size_t v_sz_boxed_2398_; size_t v_i_boxed_2399_; lean_object* v_res_2400_; 
v_sz_boxed_2398_ = lean_unbox_usize(v_sz_2383_);
lean_dec(v_sz_2383_);
v_i_boxed_2399_ = lean_unbox_usize(v_i_2384_);
lean_dec(v_i_2384_);
v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_2382_, v_sz_boxed_2398_, v_i_boxed_2399_, v_b_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v_as_2382_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_2401_, size_t v_sz_2402_, size_t v_i_2403_, lean_object* v_b_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
uint8_t v___x_2417_; 
v___x_2417_ = lean_usize_dec_lt(v_i_2403_, v_sz_2402_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_b_2404_);
return v___x_2418_;
}
else
{
lean_object* v_snd_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2443_; 
v_snd_2419_ = lean_ctor_get(v_b_2404_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_b_2404_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; 
v_unused_2444_ = lean_ctor_get(v_b_2404_, 0);
lean_dec(v_unused_2444_);
v___x_2421_ = v_b_2404_;
v_isShared_2422_ = v_isSharedCheck_2443_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_snd_2419_);
lean_dec(v_b_2404_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2443_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_a_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_a_2423_ = lean_array_uget_borrowed(v_as_2401_, v_i_2403_);
v___x_2424_ = lean_box(0);
v___x_2425_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2419_, v_a_2423_, v___x_2424_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_dec_ref_known(v___x_2425_, 1);
v___x_2426_ = lean_box(0);
v___x_2427_ = lean_unsigned_to_nat(1u);
v___x_2428_ = lean_nat_add(v_snd_2419_, v___x_2427_);
lean_dec(v_snd_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v___x_2428_);
lean_ctor_set(v___x_2421_, 0, v___x_2426_);
v___x_2430_ = v___x_2421_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = ((size_t)1ULL);
v___x_2432_ = lean_usize_add(v_i_2403_, v___x_2431_);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_2401_, v_sz_2402_, v___x_2432_, v___x_2430_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2433_;
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_del_object(v___x_2421_);
lean_dec(v_snd_2419_);
v_a_2435_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2425_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2425_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_2445_, lean_object* v_sz_2446_, lean_object* v_i_2447_, lean_object* v_b_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
size_t v_sz_boxed_2461_; size_t v_i_boxed_2462_; lean_object* v_res_2463_; 
v_sz_boxed_2461_ = lean_unbox_usize(v_sz_2446_);
lean_dec(v_sz_2446_);
v_i_boxed_2462_ = lean_unbox_usize(v_i_2447_);
lean_dec(v_i_2447_);
v_res_2463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_2445_, v_sz_boxed_2461_, v_i_boxed_2462_, v_b_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v_as_2445_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_init_2464_, lean_object* v_n_2465_, lean_object* v_b_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
if (lean_obj_tag(v_n_2465_) == 0)
{
lean_object* v_cs_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; size_t v_sz_2482_; size_t v___x_2483_; lean_object* v___x_2484_; 
v_cs_2479_ = lean_ctor_get(v_n_2465_, 0);
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v_b_2466_);
v_sz_2482_ = lean_array_size(v_cs_2479_);
v___x_2483_ = ((size_t)0ULL);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_2464_, v_cs_2479_, v_sz_2482_, v___x_2483_, v___x_2481_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2499_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_fst_2489_; 
v_fst_2489_ = lean_ctor_get(v_a_2485_, 0);
if (lean_obj_tag(v_fst_2489_) == 0)
{
lean_object* v_snd_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v_snd_2490_ = lean_ctor_get(v_a_2485_, 1);
lean_inc(v_snd_2490_);
lean_dec(v_a_2485_);
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_snd_2490_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2491_);
v___x_2493_ = v___x_2487_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
else
{
lean_object* v_val_2495_; lean_object* v___x_2497_; 
lean_inc_ref(v_fst_2489_);
lean_dec(v_a_2485_);
v_val_2495_ = lean_ctor_get(v_fst_2489_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v_fst_2489_, 1);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v_val_2495_);
v___x_2497_ = v___x_2487_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_val_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_a_2500_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2484_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2484_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_vs_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; size_t v_sz_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v_vs_2508_ = lean_ctor_get(v_n_2465_, 0);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v_b_2466_);
v_sz_2511_ = lean_array_size(v_vs_2508_);
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_2508_, v_sz_2511_, v___x_2512_, v___x_2510_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2528_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2528_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2528_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_fst_2518_; 
v_fst_2518_ = lean_ctor_get(v_a_2514_, 0);
if (lean_obj_tag(v_fst_2518_) == 0)
{
lean_object* v_snd_2519_; lean_object* v___x_2520_; lean_object* v___x_2522_; 
v_snd_2519_ = lean_ctor_get(v_a_2514_, 1);
lean_inc(v_snd_2519_);
lean_dec(v_a_2514_);
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_snd_2519_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2520_);
v___x_2522_ = v___x_2516_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
else
{
lean_object* v_val_2524_; lean_object* v___x_2526_; 
lean_inc_ref(v_fst_2518_);
lean_dec(v_a_2514_);
v_val_2524_ = lean_ctor_get(v_fst_2518_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v_fst_2518_, 1);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v_val_2524_);
v___x_2526_ = v___x_2516_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_val_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_a_2529_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2513_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2513_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_init_2537_, lean_object* v_as_2538_, size_t v_sz_2539_, size_t v_i_2540_, lean_object* v_b_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
uint8_t v___x_2554_; 
v___x_2554_ = lean_usize_dec_lt(v_i_2540_, v_sz_2539_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_b_2541_);
return v___x_2555_;
}
else
{
lean_object* v_snd_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2590_; 
v_snd_2556_ = lean_ctor_get(v_b_2541_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_b_2541_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; 
v_unused_2591_ = lean_ctor_get(v_b_2541_, 0);
lean_dec(v_unused_2591_);
v___x_2558_ = v_b_2541_;
v_isShared_2559_ = v_isSharedCheck_2590_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_snd_2556_);
lean_dec(v_b_2541_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2590_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v_a_2560_; lean_object* v___x_2561_; 
v_a_2560_ = lean_array_uget_borrowed(v_as_2538_, v_i_2540_);
lean_inc(v_snd_2556_);
v___x_2561_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_2537_, v_a_2560_, v_snd_2556_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2581_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2581_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2581_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
if (lean_obj_tag(v_a_2562_) == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2562_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2566_);
v___x_2568_ = v___x_2558_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_snd_2556_);
v___x_2568_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2570_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2568_);
v___x_2570_ = v___x_2564_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_del_object(v___x_2564_);
lean_dec(v_snd_2556_);
v_a_2573_ = lean_ctor_get(v_a_2562_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v_a_2562_, 1);
v___x_2574_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v_a_2573_);
lean_ctor_set(v___x_2558_, 0, v___x_2574_);
v___x_2576_ = v___x_2558_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_a_2573_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
size_t v___x_2577_; size_t v___x_2578_; 
v___x_2577_ = ((size_t)1ULL);
v___x_2578_ = lean_usize_add(v_i_2540_, v___x_2577_);
v_i_2540_ = v___x_2578_;
v_b_2541_ = v___x_2576_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_del_object(v___x_2558_);
lean_dec(v_snd_2556_);
v_a_2582_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2561_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2561_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_init_2592_ = _args[0];
lean_object* v_as_2593_ = _args[1];
lean_object* v_sz_2594_ = _args[2];
lean_object* v_i_2595_ = _args[3];
lean_object* v_b_2596_ = _args[4];
lean_object* v___y_2597_ = _args[5];
lean_object* v___y_2598_ = _args[6];
lean_object* v___y_2599_ = _args[7];
lean_object* v___y_2600_ = _args[8];
lean_object* v___y_2601_ = _args[9];
lean_object* v___y_2602_ = _args[10];
lean_object* v___y_2603_ = _args[11];
lean_object* v___y_2604_ = _args[12];
lean_object* v___y_2605_ = _args[13];
lean_object* v___y_2606_ = _args[14];
lean_object* v___y_2607_ = _args[15];
lean_object* v___y_2608_ = _args[16];
_start:
{
size_t v_sz_boxed_2609_; size_t v_i_boxed_2610_; lean_object* v_res_2611_; 
v_sz_boxed_2609_ = lean_unbox_usize(v_sz_2594_);
lean_dec(v_sz_2594_);
v_i_boxed_2610_ = lean_unbox_usize(v_i_2595_);
lean_dec(v_i_2595_);
v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_2592_, v_as_2593_, v_sz_boxed_2609_, v_i_boxed_2610_, v_b_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v_as_2593_);
lean_dec(v_init_2592_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_init_2612_, lean_object* v_n_2613_, lean_object* v_b_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_2612_, v_n_2613_, v_b_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v_n_2613_);
lean_dec(v_init_2612_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(lean_object* v_t_2628_, lean_object* v_init_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_root_2642_; lean_object* v_tail_2643_; lean_object* v___x_2644_; 
v_root_2642_ = lean_ctor_get(v_t_2628_, 0);
v_tail_2643_ = lean_ctor_get(v_t_2628_, 1);
lean_inc(v_init_2629_);
v___x_2644_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_2629_, v_root_2642_, v_init_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v_init_2629_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2681_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2681_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2681_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
if (lean_obj_tag(v_a_2645_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; 
v_a_2649_ = lean_ctor_get(v_a_2645_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v_a_2645_, 1);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v_a_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; size_t v_sz_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
lean_del_object(v___x_2647_);
v_a_2653_ = lean_ctor_get(v_a_2645_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v_a_2645_, 1);
v___x_2654_ = lean_box(0);
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
lean_ctor_set(v___x_2655_, 1, v_a_2653_);
v_sz_2656_ = lean_array_size(v_tail_2643_);
v___x_2657_ = ((size_t)0ULL);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_tail_2643_, v_sz_2656_, v___x_2657_, v___x_2655_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2672_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_fst_2663_; 
v_fst_2663_ = lean_ctor_get(v_a_2659_, 0);
if (lean_obj_tag(v_fst_2663_) == 0)
{
lean_object* v_snd_2664_; lean_object* v___x_2666_; 
v_snd_2664_ = lean_ctor_get(v_a_2659_, 1);
lean_inc(v_snd_2664_);
lean_dec(v_a_2659_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v_snd_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_snd_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
else
{
lean_object* v_val_2668_; lean_object* v___x_2670_; 
lean_inc_ref(v_fst_2663_);
lean_dec(v_a_2659_);
v_val_2668_ = lean_ctor_get(v_fst_2663_, 0);
lean_inc(v_val_2668_);
lean_dec_ref_known(v_fst_2663_, 1);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v_val_2668_);
v___x_2670_ = v___x_2661_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_val_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
v_a_2673_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2658_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2658_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
v_a_2682_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2644_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2644_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_2690_, lean_object* v_init_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_t_2690_, v_init_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v_t_2690_);
return v_res_2704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1));
v___x_2708_ = lean_unsigned_to_nat(2u);
v___x_2709_ = lean_unsigned_to_nat(73u);
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0));
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2712_ = l_mkPanicMessageWithDecl(v___x_2711_, v___x_2710_, v___x_2709_, v___x_2708_, v___x_2707_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v_vars_2727_; lean_object* v_diseqs_2728_; lean_object* v_size_2729_; lean_object* v_size_2730_; uint8_t v___x_2731_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v_vars_2727_ = lean_ctor_get(v_a_2726_, 30);
lean_inc_ref(v_vars_2727_);
v_diseqs_2728_ = lean_ctor_get(v_a_2726_, 34);
lean_inc_ref(v_diseqs_2728_);
lean_dec(v_a_2726_);
v_size_2729_ = lean_ctor_get(v_vars_2727_, 2);
lean_inc(v_size_2729_);
lean_dec_ref(v_vars_2727_);
v_size_2730_ = lean_ctor_get(v_diseqs_2728_, 2);
v___x_2731_ = lean_nat_dec_eq(v_size_2729_, v_size_2730_);
lean_dec(v_size_2729_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec_ref(v_diseqs_2728_);
v___x_2732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2);
v___x_2733_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_2732_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
return v___x_2733_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_unsigned_to_nat(0u);
v___x_2735_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_diseqs_2728_, v___x_2734_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec_ref(v_diseqs_2728_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2743_; 
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v___x_2735_, 0);
lean_dec(v_unused_2744_);
v___x_2737_ = v___x_2735_;
v_isShared_2738_ = v_isSharedCheck_2743_;
goto v_resetjp_2736_;
}
else
{
lean_dec(v___x_2735_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2743_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_box(0);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2739_);
v___x_2741_ = v___x_2737_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
v_a_2745_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2735_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2735_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_a_2753_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2725_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2725_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___boxed(lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec(v_a_2761_);
return v_res_2773_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(lean_object* v_msg_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; lean_object* v___f_2789_; lean_object* v___x_5472__overap_2790_; lean_object* v___x_2791_; 
v___x_2788_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0);
v___f_2789_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2789_, 0, v___x_2788_);
v___x_5472__overap_2790_ = lean_panic_fn_borrowed(v___f_2789_, v_msg_2775_);
lean_dec_ref(v___f_2789_);
lean_inc(v___y_2786_);
lean_inc_ref(v___y_2785_);
lean_inc(v___y_2784_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
lean_inc(v___y_2780_);
lean_inc_ref(v___y_2779_);
lean_inc(v___y_2778_);
lean_inc(v___y_2777_);
lean_inc(v___y_2776_);
v___x_2791_ = lean_apply_12(v___x_5472__overap_2790_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, lean_box(0));
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___boxed(lean_object* v_msg_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v_msg_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
return v_res_2805_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3));
v___x_2808_ = lean_unsigned_to_nat(6u);
v___x_2809_ = lean_unsigned_to_nat(89u);
v___x_2810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_2811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2812_ = l_mkPanicMessageWithDecl(v___x_2811_, v___x_2810_, v___x_2809_, v___x_2808_, v___x_2807_);
return v___x_2812_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2));
v___x_2815_ = lean_unsigned_to_nat(6u);
v___x_2816_ = lean_unsigned_to_nat(87u);
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2819_ = l_mkPanicMessageWithDecl(v___x_2818_, v___x_2817_, v___x_2816_, v___x_2815_, v___x_2814_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(lean_object* v_vars_2820_, lean_object* v_x_2821_, lean_object* v_____s_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_fst_2840_; lean_object* v_snd_2841_; lean_object* v_size_2842_; uint8_t v___x_2843_; 
v_fst_2840_ = lean_ctor_get(v_x_2821_, 0);
v_snd_2841_ = lean_ctor_get(v_x_2821_, 1);
v_size_2842_ = lean_ctor_get(v_vars_2820_, 2);
v___x_2843_ = lean_nat_dec_lt(v_snd_2841_, v_size_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1);
v___x_2845_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_2844_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_dec_ref_known(v___x_2845_, 1);
goto v___jp_2835_;
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2854_ = l_Lean_instInhabitedExpr;
v___x_2855_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2854_, v_vars_2820_, v_snd_2841_);
v___x_2856_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2840_, v___x_2855_);
lean_dec(v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3);
v___x_2858_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v___x_2857_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
return v___x_2858_;
}
else
{
goto v___jp_2835_;
}
}
v___jp_2835_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2836_ = lean_unsigned_to_nat(1u);
v___x_2837_ = lean_nat_add(v_____s_2822_, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed(lean_object* v_vars_2859_, lean_object* v_x_2860_, lean_object* v_____s_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(v_vars_2859_, v_x_2860_, v_____s_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v_____s_2861_);
lean_dec_ref(v_x_2860_);
lean_dec_ref(v_vars_2859_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(lean_object* v_f_2875_, lean_object* v_s_2876_, lean_object* v_a_2877_, lean_object* v_b_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v_a_2877_);
lean_ctor_set(v___x_2891_, 1, v_b_2878_);
lean_inc(v___y_2889_);
lean_inc_ref(v___y_2888_);
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc(v___y_2885_);
lean_inc_ref(v___y_2884_);
lean_inc(v___y_2883_);
lean_inc_ref(v___y_2882_);
lean_inc(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc(v___y_2879_);
v___x_2892_ = lean_apply_14(v_f_2875_, v___x_2891_, v_s_2876_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, lean_box(0));
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2919_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2919_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2919_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
if (lean_obj_tag(v_a_2893_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2907_; 
v_a_2897_ = lean_ctor_get(v_a_2893_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_a_2893_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2899_ = v_a_2893_;
v_isShared_2900_ = v_isSharedCheck_2907_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v_a_2893_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2907_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2904_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2902_);
v___x_2904_ = v___x_2895_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2918_; 
v_a_2908_ = lean_ctor_get(v_a_2893_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_a_2893_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2910_ = v_a_2893_;
v_isShared_2911_ = v_isSharedCheck_2918_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v_a_2893_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2918_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2915_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2913_);
v___x_2915_ = v___x_2895_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
v_a_2920_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2892_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2892_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed(lean_object* v_f_2928_, lean_object* v_s_2929_, lean_object* v_a_2930_, lean_object* v_b_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(v_f_2928_, v_s_2929_, v_a_2930_, v_b_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_2945_, lean_object* v_keys_2946_, lean_object* v_vals_2947_, lean_object* v_i_2948_, lean_object* v_acc_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = lean_array_get_size(v_keys_2946_);
v___x_2963_ = lean_nat_dec_lt(v_i_2948_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v_i_2948_);
lean_dec_ref(v_f_2945_);
v___x_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2964_, 0, v_acc_2949_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
else
{
lean_object* v_k_2966_; lean_object* v_v_2967_; lean_object* v___x_2968_; 
v_k_2966_ = lean_array_fget_borrowed(v_keys_2946_, v_i_2948_);
v_v_2967_ = lean_array_fget_borrowed(v_vals_2947_, v_i_2948_);
lean_inc_ref(v_f_2945_);
lean_inc(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc(v___y_2958_);
lean_inc_ref(v___y_2957_);
lean_inc(v___y_2956_);
lean_inc_ref(v___y_2955_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc(v___y_2951_);
lean_inc(v___y_2950_);
lean_inc(v_v_2967_);
lean_inc(v_k_2966_);
v___x_2968_ = lean_apply_15(v_f_2945_, v_acc_2949_, v_k_2966_, v_v_2967_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, lean_box(0));
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
if (lean_obj_tag(v_a_2969_) == 0)
{
lean_dec_ref_known(v_a_2969_, 1);
lean_dec(v_i_2948_);
lean_dec_ref(v_f_2945_);
return v___x_2968_;
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_dec_ref_known(v___x_2968_, 1);
v_a_2970_ = lean_ctor_get(v_a_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v_a_2969_, 1);
v___x_2971_ = lean_unsigned_to_nat(1u);
v___x_2972_ = lean_nat_add(v_i_2948_, v___x_2971_);
lean_dec(v_i_2948_);
v_i_2948_ = v___x_2972_;
v_acc_2949_ = v_a_2970_;
goto _start;
}
}
else
{
lean_dec(v_i_2948_);
lean_dec_ref(v_f_2945_);
return v___x_2968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_f_2974_ = _args[0];
lean_object* v_keys_2975_ = _args[1];
lean_object* v_vals_2976_ = _args[2];
lean_object* v_i_2977_ = _args[3];
lean_object* v_acc_2978_ = _args[4];
lean_object* v___y_2979_ = _args[5];
lean_object* v___y_2980_ = _args[6];
lean_object* v___y_2981_ = _args[7];
lean_object* v___y_2982_ = _args[8];
lean_object* v___y_2983_ = _args[9];
lean_object* v___y_2984_ = _args[10];
lean_object* v___y_2985_ = _args[11];
lean_object* v___y_2986_ = _args[12];
lean_object* v___y_2987_ = _args[13];
lean_object* v___y_2988_ = _args[14];
lean_object* v___y_2989_ = _args[15];
lean_object* v___y_2990_ = _args[16];
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_2974_, v_keys_2975_, v_vals_2976_, v_i_2977_, v_acc_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v_vals_2976_);
lean_dec_ref(v_keys_2975_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
if (lean_obj_tag(v_x_2993_) == 0)
{
lean_object* v_es_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3029_; 
v_es_3007_ = lean_ctor_get(v_x_2993_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_x_2993_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3009_ = v_x_2993_;
v_isShared_3010_ = v_isSharedCheck_3029_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_es_3007_);
lean_dec(v_x_2993_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3029_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_array_get_size(v_es_3007_);
v___x_3013_ = lean_nat_dec_lt(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3015_; 
lean_dec_ref(v_es_3007_);
lean_dec_ref(v_f_2992_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set_tag(v___x_3009_, 1);
lean_ctor_set(v___x_3009_, 0, v_x_2994_);
v___x_3015_ = v___x_3009_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_x_2994_);
v___x_3015_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
return v___x_3016_;
}
}
else
{
uint8_t v___x_3018_; 
v___x_3018_ = lean_nat_dec_le(v___x_3012_, v___x_3012_);
if (v___x_3018_ == 0)
{
if (v___x_3013_ == 0)
{
lean_object* v___x_3020_; 
lean_dec_ref(v_es_3007_);
lean_dec_ref(v_f_2992_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set_tag(v___x_3009_, 1);
lean_ctor_set(v___x_3009_, 0, v_x_2994_);
v___x_3020_ = v___x_3009_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_x_2994_);
v___x_3020_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
return v___x_3021_;
}
}
else
{
size_t v___x_3023_; size_t v___x_3024_; lean_object* v___x_3025_; 
lean_del_object(v___x_3009_);
v___x_3023_ = ((size_t)0ULL);
v___x_3024_ = lean_usize_of_nat(v___x_3012_);
v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2992_, v_es_3007_, v___x_3023_, v___x_3024_, v_x_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec_ref(v_es_3007_);
return v___x_3025_;
}
}
else
{
size_t v___x_3026_; size_t v___x_3027_; lean_object* v___x_3028_; 
lean_del_object(v___x_3009_);
v___x_3026_ = ((size_t)0ULL);
v___x_3027_ = lean_usize_of_nat(v___x_3012_);
v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_2992_, v_es_3007_, v___x_3026_, v___x_3027_, v_x_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec_ref(v_es_3007_);
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_ks_3030_; lean_object* v_vs_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_ks_3030_ = lean_ctor_get(v_x_2993_, 0);
lean_inc_ref(v_ks_3030_);
v_vs_3031_ = lean_ctor_get(v_x_2993_, 1);
lean_inc_ref(v_vs_3031_);
lean_dec_ref_known(v_x_2993_, 2);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_2992_, v_ks_3030_, v_vs_3031_, v___x_3032_, v_x_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec_ref(v_vs_3031_);
lean_dec_ref(v_ks_3030_);
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_3034_, lean_object* v_as_3035_, size_t v_i_3036_, size_t v_stop_3037_, lean_object* v_b_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_a_3052_; lean_object* v___y_3057_; uint8_t v___x_3060_; 
v___x_3060_ = lean_usize_dec_eq(v_i_3036_, v_stop_3037_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_array_uget_borrowed(v_as_3035_, v_i_3036_);
switch(lean_obj_tag(v___x_3061_))
{
case 0:
{
lean_object* v_key_3062_; lean_object* v_val_3063_; lean_object* v___x_3064_; 
v_key_3062_ = lean_ctor_get(v___x_3061_, 0);
v_val_3063_ = lean_ctor_get(v___x_3061_, 1);
lean_inc_ref(v_f_3034_);
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
lean_inc(v___y_3047_);
lean_inc_ref(v___y_3046_);
lean_inc(v___y_3045_);
lean_inc_ref(v___y_3044_);
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3042_);
lean_inc(v___y_3041_);
lean_inc(v___y_3040_);
lean_inc(v___y_3039_);
lean_inc(v_val_3063_);
lean_inc(v_key_3062_);
v___x_3064_ = lean_apply_15(v_f_3034_, v_b_3038_, v_key_3062_, v_val_3063_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, lean_box(0));
v___y_3057_ = v___x_3064_;
goto v___jp_3056_;
}
case 1:
{
lean_object* v_node_3065_; lean_object* v___x_3066_; 
v_node_3065_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_node_3065_);
lean_inc_ref(v_f_3034_);
v___x_3066_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3034_, v_node_3065_, v_b_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
v___y_3057_ = v___x_3066_;
goto v___jp_3056_;
}
default: 
{
v_a_3052_ = v_b_3038_;
goto v___jp_3051_;
}
}
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec_ref(v_f_3034_);
v___x_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_b_3038_);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
v___jp_3051_:
{
size_t v___x_3053_; size_t v___x_3054_; 
v___x_3053_ = ((size_t)1ULL);
v___x_3054_ = lean_usize_add(v_i_3036_, v___x_3053_);
v_i_3036_ = v___x_3054_;
v_b_3038_ = v_a_3052_;
goto _start;
}
v___jp_3056_:
{
if (lean_obj_tag(v___y_3057_) == 0)
{
lean_object* v_a_3058_; 
v_a_3058_ = lean_ctor_get(v___y_3057_, 0);
if (lean_obj_tag(v_a_3058_) == 0)
{
lean_dec_ref(v_f_3034_);
return v___y_3057_;
}
else
{
lean_object* v_a_3059_; 
lean_inc_ref(v_a_3058_);
lean_dec_ref_known(v___y_3057_, 1);
v_a_3059_ = lean_ctor_get(v_a_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v_a_3058_, 1);
v_a_3052_ = v_a_3059_;
goto v___jp_3051_;
}
}
else
{
lean_dec_ref(v_f_3034_);
return v___y_3057_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object** _args){
lean_object* v_f_3069_ = _args[0];
lean_object* v_as_3070_ = _args[1];
lean_object* v_i_3071_ = _args[2];
lean_object* v_stop_3072_ = _args[3];
lean_object* v_b_3073_ = _args[4];
lean_object* v___y_3074_ = _args[5];
lean_object* v___y_3075_ = _args[6];
lean_object* v___y_3076_ = _args[7];
lean_object* v___y_3077_ = _args[8];
lean_object* v___y_3078_ = _args[9];
lean_object* v___y_3079_ = _args[10];
lean_object* v___y_3080_ = _args[11];
lean_object* v___y_3081_ = _args[12];
lean_object* v___y_3082_ = _args[13];
lean_object* v___y_3083_ = _args[14];
lean_object* v___y_3084_ = _args[15];
lean_object* v___y_3085_ = _args[16];
_start:
{
size_t v_i_boxed_3086_; size_t v_stop_boxed_3087_; lean_object* v_res_3088_; 
v_i_boxed_3086_ = lean_unbox_usize(v_i_3071_);
lean_dec(v_i_3071_);
v_stop_boxed_3087_ = lean_unbox_usize(v_stop_3072_);
lean_dec(v_stop_3072_);
v_res_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3069_, v_as_3070_, v_i_boxed_3086_, v_stop_boxed_3087_, v_b_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v_as_3070_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_3089_, lean_object* v_x_3090_, lean_object* v_x_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3089_, v_x_3090_, v_x_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec(v___y_3092_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(lean_object* v_map_3105_, lean_object* v_init_3106_, lean_object* v_f_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v___f_3120_; lean_object* v___x_3121_; 
v___f_3120_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed), 16, 1);
lean_closure_set(v___f_3120_, 0, v_f_3107_);
lean_inc_ref(v_map_3105_);
v___x_3121_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v___f_3120_, v_map_3105_, v_init_3106_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3130_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3130_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3130_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v_a_3126_; lean_object* v___x_3128_; 
v_a_3126_ = lean_ctor_get(v_a_3122_, 0);
lean_inc(v_a_3126_);
lean_dec(v_a_3122_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v_a_3126_);
v___x_3128_ = v___x_3124_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
v_a_3131_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3121_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3121_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___boxed(lean_object* v_map_3139_, lean_object* v_init_3140_, lean_object* v_f_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_3139_, v_init_3140_, v_f_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v_map_3139_);
return v_res_3154_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0));
v___x_3157_ = lean_unsigned_to_nat(2u);
v___x_3158_ = lean_unsigned_to_nat(91u);
v___x_3159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_3160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_3161_ = l_mkPanicMessageWithDecl(v___x_3160_, v___x_3159_, v___x_3158_, v___x_3157_, v___x_3156_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v_vars_3176_; lean_object* v_varMap_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
v_vars_3176_ = lean_ctor_get(v_a_3175_, 30);
lean_inc_ref_n(v_vars_3176_, 2);
v_varMap_3177_ = lean_ctor_get(v_a_3175_, 31);
lean_inc_ref(v_varMap_3177_);
lean_dec(v_a_3175_);
v___f_3178_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed), 15, 1);
lean_closure_set(v___f_3178_, 0, v_vars_3176_);
v___x_3179_ = lean_unsigned_to_nat(0u);
v___x_3180_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_varMap_3177_, v___x_3179_, v___f_3178_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
lean_dec_ref(v_varMap_3177_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3193_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3193_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3193_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_size_3185_; uint8_t v___x_3186_; 
v_size_3185_ = lean_ctor_get(v_vars_3176_, 2);
lean_inc(v_size_3185_);
lean_dec_ref(v_vars_3176_);
v___x_3186_ = lean_nat_dec_eq(v_size_3185_, v_a_3181_);
lean_dec(v_a_3181_);
lean_dec(v_size_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_del_object(v___x_3183_);
v___x_3187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1);
v___x_3188_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3187_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
return v___x_3188_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_box(0);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3189_);
v___x_3191_ = v___x_3183_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v_vars_3176_);
v_a_3194_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3180_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3180_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
v_a_3202_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3174_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3174_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___boxed(lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec(v_a_3210_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(lean_object* v_00_u03c3_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_map_3225_, lean_object* v_init_3226_, lean_object* v_f_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_3225_, v_init_3226_, v_f_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_3241_ = _args[0];
lean_object* v_00_u03b2_3242_ = _args[1];
lean_object* v_map_3243_ = _args[2];
lean_object* v_init_3244_ = _args[3];
lean_object* v_f_3245_ = _args[4];
lean_object* v___y_3246_ = _args[5];
lean_object* v___y_3247_ = _args[6];
lean_object* v___y_3248_ = _args[7];
lean_object* v___y_3249_ = _args[8];
lean_object* v___y_3250_ = _args[9];
lean_object* v___y_3251_ = _args[10];
lean_object* v___y_3252_ = _args[11];
lean_object* v___y_3253_ = _args[12];
lean_object* v___y_3254_ = _args[13];
lean_object* v___y_3255_ = _args[14];
lean_object* v___y_3256_ = _args[15];
lean_object* v___y_3257_ = _args[16];
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(v_00_u03c3_3241_, v_00_u03b2_3242_, v_map_3243_, v_init_3244_, v_f_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v_map_3243_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(lean_object* v_map_3259_, lean_object* v_f_3260_, lean_object* v_init_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3260_, v_map_3259_, v_init_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg___boxed(lean_object* v_map_3275_, lean_object* v_f_3276_, lean_object* v_init_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(v_map_3275_, v_f_3276_, v_init_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec(v___y_3278_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(lean_object* v_00_u03c3_3291_, lean_object* v_00_u03c3_3292_, lean_object* v_00_u03b2_3293_, lean_object* v_map_3294_, lean_object* v_f_3295_, lean_object* v_init_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3295_, v_map_3294_, v_init_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_3310_ = _args[0];
lean_object* v_00_u03c3_3311_ = _args[1];
lean_object* v_00_u03b2_3312_ = _args[2];
lean_object* v_map_3313_ = _args[3];
lean_object* v_f_3314_ = _args[4];
lean_object* v_init_3315_ = _args[5];
lean_object* v___y_3316_ = _args[6];
lean_object* v___y_3317_ = _args[7];
lean_object* v___y_3318_ = _args[8];
lean_object* v___y_3319_ = _args[9];
lean_object* v___y_3320_ = _args[10];
lean_object* v___y_3321_ = _args[11];
lean_object* v___y_3322_ = _args[12];
lean_object* v___y_3323_ = _args[13];
lean_object* v___y_3324_ = _args[14];
lean_object* v___y_3325_ = _args[15];
lean_object* v___y_3326_ = _args[16];
lean_object* v___y_3327_ = _args[17];
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(v_00_u03c3_3310_, v_00_u03c3_3311_, v_00_u03b2_3312_, v_map_3313_, v_f_3314_, v_init_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_3329_, lean_object* v_00_u03c3_3330_, lean_object* v_00_u03b1_3331_, lean_object* v_00_u03b2_3332_, lean_object* v_f_3333_, lean_object* v_x_3334_, lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3333_, v_x_3334_, v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_3349_ = _args[0];
lean_object* v_00_u03c3_3350_ = _args[1];
lean_object* v_00_u03b1_3351_ = _args[2];
lean_object* v_00_u03b2_3352_ = _args[3];
lean_object* v_f_3353_ = _args[4];
lean_object* v_x_3354_ = _args[5];
lean_object* v_x_3355_ = _args[6];
lean_object* v___y_3356_ = _args[7];
lean_object* v___y_3357_ = _args[8];
lean_object* v___y_3358_ = _args[9];
lean_object* v___y_3359_ = _args[10];
lean_object* v___y_3360_ = _args[11];
lean_object* v___y_3361_ = _args[12];
lean_object* v___y_3362_ = _args[13];
lean_object* v___y_3363_ = _args[14];
lean_object* v___y_3364_ = _args[15];
lean_object* v___y_3365_ = _args[16];
lean_object* v___y_3366_ = _args[17];
lean_object* v___y_3367_ = _args[18];
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(v_00_u03c3_3349_, v_00_u03c3_3350_, v_00_u03b1_3351_, v_00_u03b2_3352_, v_f_3353_, v_x_3354_, v_x_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v___y_3356_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_3369_, lean_object* v_00_u03b2_3370_, lean_object* v_00_u03c3_3371_, lean_object* v_00_u03c3_3372_, lean_object* v_f_3373_, lean_object* v_as_3374_, size_t v_i_3375_, size_t v_stop_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3373_, v_as_3374_, v_i_3375_, v_stop_3376_, v_b_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03b1_3391_ = _args[0];
lean_object* v_00_u03b2_3392_ = _args[1];
lean_object* v_00_u03c3_3393_ = _args[2];
lean_object* v_00_u03c3_3394_ = _args[3];
lean_object* v_f_3395_ = _args[4];
lean_object* v_as_3396_ = _args[5];
lean_object* v_i_3397_ = _args[6];
lean_object* v_stop_3398_ = _args[7];
lean_object* v_b_3399_ = _args[8];
lean_object* v___y_3400_ = _args[9];
lean_object* v___y_3401_ = _args[10];
lean_object* v___y_3402_ = _args[11];
lean_object* v___y_3403_ = _args[12];
lean_object* v___y_3404_ = _args[13];
lean_object* v___y_3405_ = _args[14];
lean_object* v___y_3406_ = _args[15];
lean_object* v___y_3407_ = _args[16];
lean_object* v___y_3408_ = _args[17];
lean_object* v___y_3409_ = _args[18];
lean_object* v___y_3410_ = _args[19];
lean_object* v___y_3411_ = _args[20];
_start:
{
size_t v_i_boxed_3412_; size_t v_stop_boxed_3413_; lean_object* v_res_3414_; 
v_i_boxed_3412_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_stop_boxed_3413_ = lean_unbox_usize(v_stop_3398_);
lean_dec(v_stop_3398_);
v_res_3414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_3391_, v_00_u03b2_3392_, v_00_u03c3_3393_, v_00_u03c3_3394_, v_f_3395_, v_as_3396_, v_i_boxed_3412_, v_stop_boxed_3413_, v_b_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v_as_3396_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_3415_, lean_object* v_00_u03c3_3416_, lean_object* v_00_u03b1_3417_, lean_object* v_00_u03b2_3418_, lean_object* v_f_3419_, lean_object* v_keys_3420_, lean_object* v_vals_3421_, lean_object* v_heq_3422_, lean_object* v_i_3423_, lean_object* v_acc_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3419_, v_keys_3420_, v_vals_3421_, v_i_3423_, v_acc_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03c3_3438_ = _args[0];
lean_object* v_00_u03c3_3439_ = _args[1];
lean_object* v_00_u03b1_3440_ = _args[2];
lean_object* v_00_u03b2_3441_ = _args[3];
lean_object* v_f_3442_ = _args[4];
lean_object* v_keys_3443_ = _args[5];
lean_object* v_vals_3444_ = _args[6];
lean_object* v_heq_3445_ = _args[7];
lean_object* v_i_3446_ = _args[8];
lean_object* v_acc_3447_ = _args[9];
lean_object* v___y_3448_ = _args[10];
lean_object* v___y_3449_ = _args[11];
lean_object* v___y_3450_ = _args[12];
lean_object* v___y_3451_ = _args[13];
lean_object* v___y_3452_ = _args[14];
lean_object* v___y_3453_ = _args[15];
lean_object* v___y_3454_ = _args[16];
lean_object* v___y_3455_ = _args[17];
lean_object* v___y_3456_ = _args[18];
lean_object* v___y_3457_ = _args[19];
lean_object* v___y_3458_ = _args[20];
lean_object* v___y_3459_ = _args[21];
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_3438_, v_00_u03c3_3439_, v_00_u03b1_3440_, v_00_u03b2_3441_, v_f_3442_, v_keys_3443_, v_vals_3444_, v_heq_3445_, v_i_3446_, v_acc_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v_vals_3444_);
lean_dec_ref(v_keys_3443_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref_known(v___x_3473_, 1);
v___x_3474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v___x_3475_; 
lean_dec_ref_known(v___x_3474_, 1);
v___x_3475_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3476_; 
lean_dec_ref_known(v___x_3475_, 1);
v___x_3476_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
return v___x_3476_;
}
else
{
return v___x_3475_;
}
}
else
{
return v___x_3474_;
}
}
else
{
return v___x_3473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs___boxed(lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec(v_a_3477_);
return v_res_3489_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3492_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1));
v___x_3493_ = lean_unsigned_to_nat(6u);
v___x_3494_ = lean_unsigned_to_nat(103u);
v___x_3495_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0));
v___x_3496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_3497_ = l_mkPanicMessageWithDecl(v___x_3496_, v___x_3495_, v___x_3494_, v___x_3493_, v___x_3492_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(lean_object* v_upperBound_3498_, lean_object* v_a_3499_, lean_object* v_b_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
uint8_t v___x_3512_; 
v___x_3512_ = lean_nat_dec_lt(v_a_3499_, v_upperBound_3498_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
lean_dec(v_a_3499_);
v___x_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_b_3500_);
return v___x_3513_;
}
else
{
lean_object* v___x_3514_; lean_object* v___y_3516_; uint8_t v___x_3520_; 
v___x_3514_ = lean_box(0);
v___x_3520_ = lean_nat_dec_eq(v_a_3499_, v_a_3499_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2);
v___x_3522_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3521_, v_a_3499_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
v___y_3516_ = v___x_3522_;
goto v___jp_3515_;
}
else
{
lean_object* v___x_3523_; 
v___x_3523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_3499_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
v___y_3516_ = v___x_3523_;
goto v___jp_3515_;
}
v___jp_3515_:
{
if (lean_obj_tag(v___y_3516_) == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
lean_dec_ref_known(v___y_3516_, 1);
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_nat_add(v_a_3499_, v___x_3517_);
lean_dec(v_a_3499_);
v_a_3499_ = v___x_3518_;
v_b_3500_ = v___x_3514_;
goto _start;
}
else
{
lean_dec(v_a_3499_);
return v___y_3516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___boxed(lean_object* v_upperBound_3524_, lean_object* v_a_3525_, lean_object* v_b_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_3524_, v_a_3525_, v_b_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec(v_upperBound_3524_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants(lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
uint8_t v_debug_3550_; 
v_debug_3550_ = lean_ctor_get_uint8(v_a_3541_, sizeof(void*)*8 + 2);
if (v_debug_3550_ == 0)
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = lean_box(0);
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
else
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_3539_, v_a_3547_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v_structs_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v_structs_3555_ = lean_ctor_get(v_a_3554_, 0);
lean_inc_ref(v_structs_3555_);
lean_dec(v_a_3554_);
v___x_3556_ = lean_array_get_size(v_structs_3555_);
lean_dec_ref(v_structs_3555_);
v___x_3557_ = lean_unsigned_to_nat(0u);
v___x_3558_ = lean_box(0);
v___x_3559_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v___x_3556_, v___x_3557_, v___x_3558_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v___x_3559_, 0);
lean_dec(v_unused_3567_);
v___x_3561_ = v___x_3559_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_dec(v___x_3559_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3558_);
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3558_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
else
{
return v___x_3559_;
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
v_a_3568_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3553_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3553_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed(lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Meta_Grind_Arith_Linear_checkInvariants(v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec(v_a_3576_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(lean_object* v_upperBound_3588_, lean_object* v_inst_3589_, lean_object* v_R_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_, lean_object* v_c_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_3588_, v_a_3591_, v_b_3592_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_3606_ = _args[0];
lean_object* v_inst_3607_ = _args[1];
lean_object* v_R_3608_ = _args[2];
lean_object* v_a_3609_ = _args[3];
lean_object* v_b_3610_ = _args[4];
lean_object* v_c_3611_ = _args[5];
lean_object* v___y_3612_ = _args[6];
lean_object* v___y_3613_ = _args[7];
lean_object* v___y_3614_ = _args[8];
lean_object* v___y_3615_ = _args[9];
lean_object* v___y_3616_ = _args[10];
lean_object* v___y_3617_ = _args[11];
lean_object* v___y_3618_ = _args[12];
lean_object* v___y_3619_ = _args[13];
lean_object* v___y_3620_ = _args[14];
lean_object* v___y_3621_ = _args[15];
lean_object* v___y_3622_ = _args[16];
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(v_upperBound_3606_, v_inst_3607_, v_R_3608_, v_a_3609_, v_b_3610_, v_c_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec(v_upperBound_3606_);
return v_res_3623_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
