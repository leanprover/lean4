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
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 123, .m_capacity = 123, .m_length = 122, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.2982430543._hygCtx._hyg.67.0 ).contains y\n    "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "assertion violation: !( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Linear.Inv.341169003._hygCtx._hyg.34.0 )\n  "};
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_57_; lean_object* v___f_58_; lean_object* v___x_2201__overap_59_; lean_object* v___x_60_; 
v___x_57_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0);
v___f_58_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_58_, 0, v___x_57_);
v___x_2201__overap_59_ = lean_panic_fn(v___f_58_, v_msg_44_);
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
lean_dec_ref(v___x_114_);
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
lean_dec_ref(v___x_209_);
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
lean_dec_ref(v___x_308_);
v___x_310_ = lean_unbox(v_a_309_);
lean_dec(v_a_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_268_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v___x_311_);
v___x_312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(v_p_268_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_dec_ref(v___x_312_);
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
lean_object* v___x_350_; lean_object* v___f_351_; lean_object* v___x_4606__overap_352_; lean_object* v___x_353_; 
v___x_350_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0);
v___f_351_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_351_, 0, v___x_350_);
v___x_4606__overap_352_ = lean_panic_fn(v___f_351_, v_msg_337_);
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
v___x_353_ = lean_apply_12(v___x_4606__overap_352_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, lean_box(0));
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
lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_464_; 
v_snd_402_ = lean_ctor_get(v_b_387_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_b_387_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_b_387_, 0);
lean_dec(v_unused_465_);
v___x_404_ = v_b_387_;
v_isShared_405_ = v_isSharedCheck_464_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_dec(v_b_387_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_464_;
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
lean_object* v___x_409_; lean_object* v_a_411_; lean_object* v___x_440_; uint8_t v___y_442_; 
lean_dec_ref(v___x_408_);
v___x_409_ = lean_box(0);
v___x_440_ = lean_box(0);
if (lean_obj_tag(v_p_407_) == 1)
{
lean_object* v_k_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_k_443_ = lean_ctor_get(v_p_407_, 0);
v___x_444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_445_ = lean_int_dec_lt(v_k_443_, v___x_444_);
if (v_isLower_383_ == 0)
{
if (v___x_445_ == 0)
{
v___y_442_ = v___x_400_;
goto v___jp_441_;
}
else
{
goto v___jp_418_;
}
}
else
{
v___y_442_ = v___x_445_;
goto v___jp_441_;
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_snd_402_);
v___x_446_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_447_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_446_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_dec_ref(v___x_447_);
v_a_411_ = v___x_440_;
goto v___jp_410_;
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_del_object(v___x_404_);
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
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
v___jp_418_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_420_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_419_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_431_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
if (lean_obj_tag(v_a_421_) == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
lean_del_object(v___x_404_);
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v_a_421_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_snd_402_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_426_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
else
{
lean_object* v_a_430_; 
lean_del_object(v___x_423_);
lean_dec(v_snd_402_);
v_a_430_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_a_430_);
lean_dec_ref(v_a_421_);
v_a_411_ = v_a_430_;
goto v___jp_410_;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
v_a_432_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_420_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_420_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
v___jp_441_:
{
if (v___y_442_ == 0)
{
goto v___jp_418_;
}
else
{
lean_dec(v_snd_402_);
v_a_411_ = v___x_440_;
goto v___jp_410_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
v_a_456_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_408_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_408_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_____s_466_ = _args[0];
lean_object* v_isLower_467_ = _args[1];
lean_object* v_as_468_ = _args[2];
lean_object* v_sz_469_ = _args[3];
lean_object* v_i_470_ = _args[4];
lean_object* v_b_471_ = _args[5];
lean_object* v___y_472_ = _args[6];
lean_object* v___y_473_ = _args[7];
lean_object* v___y_474_ = _args[8];
lean_object* v___y_475_ = _args[9];
lean_object* v___y_476_ = _args[10];
lean_object* v___y_477_ = _args[11];
lean_object* v___y_478_ = _args[12];
lean_object* v___y_479_ = _args[13];
lean_object* v___y_480_ = _args[14];
lean_object* v___y_481_ = _args[15];
lean_object* v___y_482_ = _args[16];
lean_object* v___y_483_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_484_; size_t v_sz_boxed_485_; size_t v_i_boxed_486_; lean_object* v_res_487_; 
v_isLower_boxed_484_ = lean_unbox(v_isLower_467_);
v_sz_boxed_485_ = lean_unbox_usize(v_sz_469_);
lean_dec(v_sz_469_);
v_i_boxed_486_ = lean_unbox_usize(v_i_470_);
lean_dec(v_i_470_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_466_, v_isLower_boxed_484_, v_as_468_, v_sz_boxed_485_, v_i_boxed_486_, v_b_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v_as_468_);
lean_dec(v_____s_466_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object* v_____s_488_, uint8_t v_isLower_489_, lean_object* v_as_490_, size_t v_sz_491_, size_t v_i_492_, lean_object* v_b_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v_b_493_);
return v___x_507_;
}
else
{
lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_570_; 
v_snd_508_ = lean_ctor_get(v_b_493_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_b_493_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v_b_493_, 0);
lean_dec(v_unused_571_);
v___x_510_ = v_b_493_;
v_isShared_511_ = v_isSharedCheck_570_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_dec(v_b_493_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_570_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_a_512_; lean_object* v_p_513_; lean_object* v___x_514_; 
v_a_512_ = lean_array_uget_borrowed(v_as_490_, v_i_492_);
v_p_513_ = lean_ctor_get(v_a_512_, 0);
v___x_514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_513_, v_____s_488_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_a_518_; uint8_t v___y_548_; 
lean_dec_ref(v___x_514_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_box(0);
if (lean_obj_tag(v_p_513_) == 1)
{
lean_object* v_k_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_k_549_ = lean_ctor_get(v_p_513_, 0);
v___x_550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_551_ = lean_int_dec_lt(v_k_549_, v___x_550_);
if (v_isLower_489_ == 0)
{
if (v___x_551_ == 0)
{
v___y_548_ = v___x_506_;
goto v___jp_547_;
}
else
{
goto v___jp_525_;
}
}
else
{
v___y_548_ = v___x_551_;
goto v___jp_547_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_snd_508_);
v___x_552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_553_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_552_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_dec_ref(v___x_553_);
v_a_518_ = v___x_515_;
goto v___jp_517_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_del_object(v___x_510_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
v___jp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v_a_518_);
lean_ctor_set(v___x_510_, 0, v___x_516_);
v___x_520_ = v___x_510_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_a_518_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_492_, v___x_521_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_488_, v_isLower_489_, v_as_490_, v_sz_491_, v___x_522_, v___x_520_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_523_;
}
}
v___jp_525_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_527_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_526_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
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
lean_del_object(v___x_510_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v_a_528_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_snd_508_);
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
lean_dec(v_snd_508_);
v_a_537_ = lean_ctor_get(v_a_528_, 0);
lean_inc(v_a_537_);
lean_dec_ref(v_a_528_);
v_a_518_ = v_a_537_;
goto v___jp_517_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_510_);
lean_dec(v_snd_508_);
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
v___jp_547_:
{
if (v___y_548_ == 0)
{
goto v___jp_525_;
}
else
{
lean_dec(v_snd_508_);
v_a_518_ = v___x_515_;
goto v___jp_517_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_del_object(v___x_510_);
lean_dec(v_snd_508_);
v_a_562_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_514_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_514_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_____s_572_ = _args[0];
lean_object* v_isLower_573_ = _args[1];
lean_object* v_as_574_ = _args[2];
lean_object* v_sz_575_ = _args[3];
lean_object* v_i_576_ = _args[4];
lean_object* v_b_577_ = _args[5];
lean_object* v___y_578_ = _args[6];
lean_object* v___y_579_ = _args[7];
lean_object* v___y_580_ = _args[8];
lean_object* v___y_581_ = _args[9];
lean_object* v___y_582_ = _args[10];
lean_object* v___y_583_ = _args[11];
lean_object* v___y_584_ = _args[12];
lean_object* v___y_585_ = _args[13];
lean_object* v___y_586_ = _args[14];
lean_object* v___y_587_ = _args[15];
lean_object* v___y_588_ = _args[16];
lean_object* v___y_589_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_590_; size_t v_sz_boxed_591_; size_t v_i_boxed_592_; lean_object* v_res_593_; 
v_isLower_boxed_590_ = lean_unbox(v_isLower_573_);
v_sz_boxed_591_ = lean_unbox_usize(v_sz_575_);
lean_dec(v_sz_575_);
v_i_boxed_592_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_572_, v_isLower_boxed_590_, v_as_574_, v_sz_boxed_591_, v_i_boxed_592_, v_b_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v_as_574_);
lean_dec(v_____s_572_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(lean_object* v_____s_594_, uint8_t v_isLower_595_, lean_object* v_inh_596_, lean_object* v_n_597_, lean_object* v_b_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
if (lean_obj_tag(v_n_597_) == 0)
{
lean_object* v_cs_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_645_; 
v_cs_611_ = lean_ctor_get(v_n_597_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v_n_597_);
if (v_isSharedCheck_645_ == 0)
{
v___x_613_ = v_n_597_;
v_isShared_614_ = v_isSharedCheck_645_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_cs_611_);
lean_dec(v_n_597_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_645_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; size_t v_sz_617_; size_t v___x_618_; lean_object* v___x_619_; 
v___x_615_ = lean_box(0);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_b_598_);
v_sz_617_ = lean_array_size(v_cs_611_);
v___x_618_ = ((size_t)0ULL);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_____s_594_, v_isLower_595_, v_inh_596_, v_cs_611_, v_sz_617_, v___x_618_, v___x_616_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec_ref(v_cs_611_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_636_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_636_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_636_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_636_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_fst_624_; 
v_fst_624_ = lean_ctor_get(v_a_620_, 0);
if (lean_obj_tag(v_fst_624_) == 0)
{
lean_object* v_snd_625_; lean_object* v___x_627_; 
v_snd_625_ = lean_ctor_get(v_a_620_, 1);
lean_inc(v_snd_625_);
lean_dec(v_a_620_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 1);
lean_ctor_set(v___x_613_, 0, v_snd_625_);
v___x_627_ = v___x_613_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_snd_625_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_627_);
v___x_629_ = v___x_622_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
else
{
lean_object* v_val_632_; lean_object* v___x_634_; 
lean_inc_ref(v_fst_624_);
lean_dec(v_a_620_);
lean_del_object(v___x_613_);
v_val_632_ = lean_ctor_get(v_fst_624_, 0);
lean_inc(v_val_632_);
lean_dec_ref(v_fst_624_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v_val_632_);
v___x_634_ = v___x_622_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_val_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_del_object(v___x_613_);
v_a_637_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_619_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_619_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
else
{
lean_object* v_vs_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_680_; 
v_vs_646_ = lean_ctor_get(v_n_597_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_n_597_);
if (v_isSharedCheck_680_ == 0)
{
v___x_648_ = v_n_597_;
v_isShared_649_ = v_isSharedCheck_680_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_vs_646_);
lean_dec(v_n_597_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_680_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; size_t v_sz_652_; size_t v___x_653_; lean_object* v___x_654_; 
v___x_650_ = lean_box(0);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v_b_598_);
v_sz_652_ = lean_array_size(v_vs_646_);
v___x_653_ = ((size_t)0ULL);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_594_, v_isLower_595_, v_vs_646_, v_sz_652_, v___x_653_, v___x_651_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec_ref(v_vs_646_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_671_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_671_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_671_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_671_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_fst_659_; 
v_fst_659_ = lean_ctor_get(v_a_655_, 0);
if (lean_obj_tag(v_fst_659_) == 0)
{
lean_object* v_snd_660_; lean_object* v___x_662_; 
v_snd_660_ = lean_ctor_get(v_a_655_, 1);
lean_inc(v_snd_660_);
lean_dec(v_a_655_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v_snd_660_);
v___x_662_ = v___x_648_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_snd_660_);
v___x_662_ = v_reuseFailAlloc_666_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_662_);
v___x_664_ = v___x_657_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_val_667_; lean_object* v___x_669_; 
lean_inc_ref(v_fst_659_);
lean_dec(v_a_655_);
lean_del_object(v___x_648_);
v_val_667_ = lean_ctor_get(v_fst_659_, 0);
lean_inc(v_val_667_);
lean_dec_ref(v_fst_659_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_val_667_);
v___x_669_ = v___x_657_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_val_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_del_object(v___x_648_);
v_a_672_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_654_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_654_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_____s_681_, uint8_t v_isLower_682_, lean_object* v_inh_683_, lean_object* v_as_684_, size_t v_sz_685_, size_t v_i_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_lt(v_i_686_, v_sz_685_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v_b_687_);
return v___x_701_;
}
else
{
lean_object* v_snd_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_736_; 
v_snd_702_ = lean_ctor_get(v_b_687_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_b_687_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v_b_687_, 0);
lean_dec(v_unused_737_);
v___x_704_ = v_b_687_;
v_isShared_705_ = v_isSharedCheck_736_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snd_702_);
lean_dec(v_b_687_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_736_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_a_706_; lean_object* v___x_707_; 
v_a_706_ = lean_array_uget_borrowed(v_as_684_, v_i_686_);
lean_inc(v_snd_702_);
lean_inc(v_a_706_);
v___x_707_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_____s_681_, v_isLower_682_, v_inh_683_, v_a_706_, v_snd_702_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_727_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_727_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_727_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_727_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
if (lean_obj_tag(v_a_708_) == 0)
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v_a_708_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_712_);
v___x_714_ = v___x_704_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_snd_702_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_714_);
v___x_716_ = v___x_710_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
lean_del_object(v___x_710_);
lean_dec(v_snd_702_);
v_a_719_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v_a_708_);
v___x_720_ = lean_box(0);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v_a_719_);
lean_ctor_set(v___x_704_, 0, v___x_720_);
v___x_722_ = v___x_704_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_a_719_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
size_t v___x_723_; size_t v___x_724_; 
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_add(v_i_686_, v___x_723_);
v_i_686_ = v___x_724_;
v_b_687_ = v___x_722_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_del_object(v___x_704_);
lean_dec(v_snd_702_);
v_a_728_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_707_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_707_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_738_ = _args[0];
lean_object* v_isLower_739_ = _args[1];
lean_object* v_inh_740_ = _args[2];
lean_object* v_as_741_ = _args[3];
lean_object* v_sz_742_ = _args[4];
lean_object* v_i_743_ = _args[5];
lean_object* v_b_744_ = _args[6];
lean_object* v___y_745_ = _args[7];
lean_object* v___y_746_ = _args[8];
lean_object* v___y_747_ = _args[9];
lean_object* v___y_748_ = _args[10];
lean_object* v___y_749_ = _args[11];
lean_object* v___y_750_ = _args[12];
lean_object* v___y_751_ = _args[13];
lean_object* v___y_752_ = _args[14];
lean_object* v___y_753_ = _args[15];
lean_object* v___y_754_ = _args[16];
lean_object* v___y_755_ = _args[17];
lean_object* v___y_756_ = _args[18];
_start:
{
uint8_t v_isLower_boxed_757_; size_t v_sz_boxed_758_; size_t v_i_boxed_759_; lean_object* v_res_760_; 
v_isLower_boxed_757_ = lean_unbox(v_isLower_739_);
v_sz_boxed_758_ = lean_unbox_usize(v_sz_742_);
lean_dec(v_sz_742_);
v_i_boxed_759_ = lean_unbox_usize(v_i_743_);
lean_dec(v_i_743_);
v_res_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_____s_738_, v_isLower_boxed_757_, v_inh_740_, v_as_741_, v_sz_boxed_758_, v_i_boxed_759_, v_b_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v_as_741_);
lean_dec(v_____s_738_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_____s_761_ = _args[0];
lean_object* v_isLower_762_ = _args[1];
lean_object* v_inh_763_ = _args[2];
lean_object* v_n_764_ = _args[3];
lean_object* v_b_765_ = _args[4];
lean_object* v___y_766_ = _args[5];
lean_object* v___y_767_ = _args[6];
lean_object* v___y_768_ = _args[7];
lean_object* v___y_769_ = _args[8];
lean_object* v___y_770_ = _args[9];
lean_object* v___y_771_ = _args[10];
lean_object* v___y_772_ = _args[11];
lean_object* v___y_773_ = _args[12];
lean_object* v___y_774_ = _args[13];
lean_object* v___y_775_ = _args[14];
lean_object* v___y_776_ = _args[15];
lean_object* v___y_777_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_778_; lean_object* v_res_779_; 
v_isLower_boxed_778_ = lean_unbox(v_isLower_762_);
v_res_779_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_____s_761_, v_isLower_boxed_778_, v_inh_763_, v_n_764_, v_b_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec(v___y_767_);
lean_dec(v___y_766_);
lean_dec(v_____s_761_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object* v_____s_780_, uint8_t v_isLower_781_, lean_object* v_as_782_, size_t v_sz_783_, size_t v_i_784_, lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_lt(v_i_784_, v_sz_783_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_b_785_);
return v___x_799_;
}
else
{
lean_object* v_snd_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_869_; 
v_snd_800_ = lean_ctor_get(v_b_785_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_b_785_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_b_785_, 0);
lean_dec(v_unused_870_);
v___x_802_ = v_b_785_;
v_isShared_803_ = v_isSharedCheck_869_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_snd_800_);
lean_dec(v_b_785_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_869_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_a_804_; lean_object* v_p_805_; lean_object* v___x_806_; 
v_a_804_ = lean_array_uget_borrowed(v_as_782_, v_i_784_);
v_p_805_ = lean_ctor_get(v_a_804_, 0);
v___x_806_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_805_, v_____s_780_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_807_; lean_object* v_a_809_; lean_object* v___x_845_; uint8_t v___y_847_; 
lean_dec_ref(v___x_806_);
v___x_807_ = lean_box(0);
v___x_845_ = lean_box(0);
if (lean_obj_tag(v_p_805_) == 1)
{
lean_object* v_k_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_k_848_ = lean_ctor_get(v_p_805_, 0);
v___x_849_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_850_ = lean_int_dec_lt(v_k_848_, v___x_849_);
if (v_isLower_781_ == 0)
{
if (v___x_850_ == 0)
{
v___y_847_ = v___x_798_;
goto v___jp_846_;
}
else
{
goto v___jp_816_;
}
}
else
{
v___y_847_ = v___x_850_;
goto v___jp_846_;
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_snd_800_);
v___x_851_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_852_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_851_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_dec_ref(v___x_852_);
v_a_809_ = v___x_845_;
goto v___jp_808_;
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_del_object(v___x_802_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
v___jp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v_a_809_);
lean_ctor_set(v___x_802_, 0, v___x_807_);
v___x_811_ = v___x_802_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_a_809_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
size_t v___x_812_; size_t v___x_813_; 
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_add(v_i_784_, v___x_812_);
v_i_784_ = v___x_813_;
v_b_785_ = v___x_811_;
goto _start;
}
}
v___jp_816_:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_818_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_817_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_836_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_836_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_836_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_836_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
if (lean_obj_tag(v_a_819_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_834_; 
lean_del_object(v___x_802_);
v_a_823_ = lean_ctor_get(v_a_819_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_834_ == 0)
{
v___x_825_ = v_a_819_;
v_isShared_826_ = v_isSharedCheck_834_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v_a_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_834_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 1);
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_833_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v_snd_800_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_829_);
v___x_831_ = v___x_821_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
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
else
{
lean_object* v_a_835_; 
lean_del_object(v___x_821_);
lean_dec(v_snd_800_);
v_a_835_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_a_835_);
lean_dec_ref(v_a_819_);
v_a_809_ = v_a_835_;
goto v___jp_808_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_802_);
lean_dec(v_snd_800_);
v_a_837_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_818_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_818_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
v___jp_846_:
{
if (v___y_847_ == 0)
{
goto v___jp_816_;
}
else
{
lean_dec(v_snd_800_);
v_a_809_ = v___x_845_;
goto v___jp_808_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_del_object(v___x_802_);
lean_dec(v_snd_800_);
v_a_861_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_806_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_806_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_____s_871_ = _args[0];
lean_object* v_isLower_872_ = _args[1];
lean_object* v_as_873_ = _args[2];
lean_object* v_sz_874_ = _args[3];
lean_object* v_i_875_ = _args[4];
lean_object* v_b_876_ = _args[5];
lean_object* v___y_877_ = _args[6];
lean_object* v___y_878_ = _args[7];
lean_object* v___y_879_ = _args[8];
lean_object* v___y_880_ = _args[9];
lean_object* v___y_881_ = _args[10];
lean_object* v___y_882_ = _args[11];
lean_object* v___y_883_ = _args[12];
lean_object* v___y_884_ = _args[13];
lean_object* v___y_885_ = _args[14];
lean_object* v___y_886_ = _args[15];
lean_object* v___y_887_ = _args[16];
lean_object* v___y_888_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_889_; size_t v_sz_boxed_890_; size_t v_i_boxed_891_; lean_object* v_res_892_; 
v_isLower_boxed_889_ = lean_unbox(v_isLower_872_);
v_sz_boxed_890_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v_i_boxed_891_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_871_, v_isLower_boxed_889_, v_as_873_, v_sz_boxed_890_, v_i_boxed_891_, v_b_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v_as_873_);
lean_dec(v_____s_871_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(lean_object* v_____s_893_, uint8_t v_isLower_894_, lean_object* v_as_895_, size_t v_sz_896_, size_t v_i_897_, lean_object* v_b_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_lt(v_i_897_, v_sz_896_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_b_898_);
return v___x_912_;
}
else
{
lean_object* v_snd_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_982_; 
v_snd_913_ = lean_ctor_get(v_b_898_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_b_898_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_b_898_, 0);
lean_dec(v_unused_983_);
v___x_915_ = v_b_898_;
v_isShared_916_ = v_isSharedCheck_982_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_snd_913_);
lean_dec(v_b_898_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_982_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_a_917_; lean_object* v_p_918_; lean_object* v___x_919_; 
v_a_917_ = lean_array_uget_borrowed(v_as_895_, v_i_897_);
v_p_918_ = lean_ctor_get(v_a_917_, 0);
v___x_919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_918_, v_____s_893_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_a_923_; uint8_t v___y_960_; 
lean_dec_ref(v___x_919_);
v___x_920_ = lean_box(0);
v___x_921_ = lean_box(0);
if (lean_obj_tag(v_p_918_) == 1)
{
lean_object* v_k_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_k_961_ = lean_ctor_get(v_p_918_, 0);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
v___x_963_ = lean_int_dec_lt(v_k_961_, v___x_962_);
if (v_isLower_894_ == 0)
{
if (v___x_963_ == 0)
{
v___y_960_ = v___x_911_;
goto v___jp_959_;
}
else
{
goto v___jp_930_;
}
}
else
{
v___y_960_ = v___x_963_;
goto v___jp_959_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_snd_913_);
v___x_964_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
v___x_965_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_964_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_dec_ref(v___x_965_);
v_a_923_ = v___x_920_;
goto v___jp_922_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_del_object(v___x_915_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
v___jp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v_a_923_);
lean_ctor_set(v___x_915_, 0, v___x_921_);
v___x_925_ = v___x_915_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_a_923_);
v___x_925_ = v_reuseFailAlloc_929_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
size_t v___x_926_; size_t v___x_927_; lean_object* v___x_928_; 
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_897_, v___x_926_);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_893_, v_isLower_894_, v_as_895_, v_sz_896_, v___x_927_, v___x_925_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
return v___x_928_;
}
}
v___jp_930_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
v___x_932_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_931_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_950_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_950_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_950_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_950_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
if (lean_obj_tag(v_a_933_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
lean_del_object(v___x_915_);
v_a_937_ = lean_ctor_get(v_a_933_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_948_ == 0)
{
v___x_939_ = v_a_933_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v_a_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 1);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_947_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v_snd_913_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_943_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
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
else
{
lean_object* v_a_949_; 
lean_del_object(v___x_935_);
lean_dec(v_snd_913_);
v_a_949_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v_a_933_);
v_a_923_ = v_a_949_;
goto v___jp_922_;
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_del_object(v___x_915_);
lean_dec(v_snd_913_);
v_a_951_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_932_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_932_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
v___jp_959_:
{
if (v___y_960_ == 0)
{
goto v___jp_930_;
}
else
{
lean_dec(v_snd_913_);
v_a_923_ = v___x_920_;
goto v___jp_922_;
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_del_object(v___x_915_);
lean_dec(v_snd_913_);
v_a_974_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_919_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_919_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_984_ = _args[0];
lean_object* v_isLower_985_ = _args[1];
lean_object* v_as_986_ = _args[2];
lean_object* v_sz_987_ = _args[3];
lean_object* v_i_988_ = _args[4];
lean_object* v_b_989_ = _args[5];
lean_object* v___y_990_ = _args[6];
lean_object* v___y_991_ = _args[7];
lean_object* v___y_992_ = _args[8];
lean_object* v___y_993_ = _args[9];
lean_object* v___y_994_ = _args[10];
lean_object* v___y_995_ = _args[11];
lean_object* v___y_996_ = _args[12];
lean_object* v___y_997_ = _args[13];
lean_object* v___y_998_ = _args[14];
lean_object* v___y_999_ = _args[15];
lean_object* v___y_1000_ = _args[16];
lean_object* v___y_1001_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_1002_; size_t v_sz_boxed_1003_; size_t v_i_boxed_1004_; lean_object* v_res_1005_; 
v_isLower_boxed_1002_ = lean_unbox(v_isLower_985_);
v_sz_boxed_1003_ = lean_unbox_usize(v_sz_987_);
lean_dec(v_sz_987_);
v_i_boxed_1004_ = lean_unbox_usize(v_i_988_);
lean_dec(v_i_988_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_984_, v_isLower_boxed_1002_, v_as_986_, v_sz_boxed_1003_, v_i_boxed_1004_, v_b_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v_as_986_);
lean_dec(v_____s_984_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(lean_object* v_____s_1006_, uint8_t v_isLower_1007_, lean_object* v_t_1008_, lean_object* v_init_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_root_1022_; lean_object* v_tail_1023_; lean_object* v___x_1024_; 
v_root_1022_ = lean_ctor_get(v_t_1008_, 0);
lean_inc_ref(v_root_1022_);
v_tail_1023_ = lean_ctor_get(v_t_1008_, 1);
lean_inc_ref(v_tail_1023_);
lean_dec_ref(v_t_1008_);
v___x_1024_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_____s_1006_, v_isLower_1007_, v_init_1009_, v_root_1022_, v_init_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1061_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1061_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1061_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
if (lean_obj_tag(v_a_1025_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; 
lean_dec_ref(v_tail_1023_);
v_a_1029_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v_a_1025_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v_a_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; size_t v_sz_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
lean_del_object(v___x_1027_);
v_a_1033_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_a_1033_);
lean_dec_ref(v_a_1025_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v_a_1033_);
v_sz_1036_ = lean_array_size(v_tail_1023_);
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_1006_, v_isLower_1007_, v_tail_1023_, v_sz_1036_, v___x_1037_, v___x_1035_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec_ref(v_tail_1023_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1052_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_fst_1043_; 
v_fst_1043_ = lean_ctor_get(v_a_1039_, 0);
if (lean_obj_tag(v_fst_1043_) == 0)
{
lean_object* v_snd_1044_; lean_object* v___x_1046_; 
v_snd_1044_ = lean_ctor_get(v_a_1039_, 1);
lean_inc(v_snd_1044_);
lean_dec(v_a_1039_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_snd_1044_);
v___x_1046_ = v___x_1041_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_snd_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
else
{
lean_object* v_val_1048_; lean_object* v___x_1050_; 
lean_inc_ref(v_fst_1043_);
lean_dec(v_a_1039_);
v_val_1048_ = lean_ctor_get(v_fst_1043_, 0);
lean_inc(v_val_1048_);
lean_dec_ref(v_fst_1043_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_val_1048_);
v___x_1050_ = v___x_1041_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_val_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1038_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1038_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_tail_1023_);
v_a_1062_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1024_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1024_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1070_, lean_object* v_isLower_1071_, lean_object* v_t_1072_, lean_object* v_init_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v_isLower_boxed_1086_; lean_object* v_res_1087_; 
v_isLower_boxed_1086_ = lean_unbox(v_isLower_1071_);
v_res_1087_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_____s_1070_, v_isLower_boxed_1086_, v_t_1072_, v_init_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec(v_____s_1070_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1088_, lean_object* v_as_1089_, size_t v_sz_1090_, size_t v_i_1091_, lean_object* v_b_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v___x_1105_; 
v___x_1105_ = lean_usize_dec_lt(v_i_1091_, v_sz_1090_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_b_1092_);
return v___x_1106_;
}
else
{
lean_object* v_snd_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1131_; 
v_snd_1107_ = lean_ctor_get(v_b_1092_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_b_1092_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v_b_1092_, 0);
lean_dec(v_unused_1132_);
v___x_1109_ = v_b_1092_;
v_isShared_1110_ = v_isSharedCheck_1131_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snd_1107_);
lean_dec(v_b_1092_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1131_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_a_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_a_1111_ = lean_array_uget_borrowed(v_as_1089_, v_i_1091_);
v___x_1112_ = lean_box(0);
lean_inc(v_a_1111_);
v___x_1113_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1107_, v_isLower_1088_, v_a_1111_, v___x_1112_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_dec_ref(v___x_1113_);
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_add(v_snd_1107_, v___x_1115_);
lean_dec(v_snd_1107_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v___x_1116_);
lean_ctor_set(v___x_1109_, 0, v___x_1114_);
v___x_1118_ = v___x_1109_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
size_t v___x_1119_; size_t v___x_1120_; 
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1091_, v___x_1119_);
v_i_1091_ = v___x_1120_;
v_b_1092_ = v___x_1118_;
goto _start;
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_del_object(v___x_1109_);
lean_dec(v_snd_1107_);
v_a_1123_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1113_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1113_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object** _args){
lean_object* v_isLower_1133_ = _args[0];
lean_object* v_as_1134_ = _args[1];
lean_object* v_sz_1135_ = _args[2];
lean_object* v_i_1136_ = _args[3];
lean_object* v_b_1137_ = _args[4];
lean_object* v___y_1138_ = _args[5];
lean_object* v___y_1139_ = _args[6];
lean_object* v___y_1140_ = _args[7];
lean_object* v___y_1141_ = _args[8];
lean_object* v___y_1142_ = _args[9];
lean_object* v___y_1143_ = _args[10];
lean_object* v___y_1144_ = _args[11];
lean_object* v___y_1145_ = _args[12];
lean_object* v___y_1146_ = _args[13];
lean_object* v___y_1147_ = _args[14];
lean_object* v___y_1148_ = _args[15];
lean_object* v___y_1149_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1150_; size_t v_sz_boxed_1151_; size_t v_i_boxed_1152_; lean_object* v_res_1153_; 
v_isLower_boxed_1150_ = lean_unbox(v_isLower_1133_);
v_sz_boxed_1151_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1152_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1150_, v_as_1134_, v_sz_boxed_1151_, v_i_boxed_1152_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v_as_1134_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1154_, lean_object* v_as_1155_, size_t v_sz_1156_, size_t v_i_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_usize_dec_lt(v_i_1157_, v_sz_1156_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_b_1158_);
return v___x_1172_;
}
else
{
lean_object* v_snd_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1197_; 
v_snd_1173_ = lean_ctor_get(v_b_1158_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_b_1158_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v_b_1158_, 0);
lean_dec(v_unused_1198_);
v___x_1175_ = v_b_1158_;
v_isShared_1176_ = v_isSharedCheck_1197_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_snd_1173_);
lean_dec(v_b_1158_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1197_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_a_1177_ = lean_array_uget_borrowed(v_as_1155_, v_i_1157_);
v___x_1178_ = lean_box(0);
lean_inc(v_a_1177_);
v___x_1179_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1173_, v_isLower_1154_, v_a_1177_, v___x_1178_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
lean_dec_ref(v___x_1179_);
v___x_1180_ = lean_box(0);
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = lean_nat_add(v_snd_1173_, v___x_1181_);
lean_dec(v_snd_1173_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1182_);
lean_ctor_set(v___x_1175_, 0, v___x_1180_);
v___x_1184_ = v___x_1175_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
size_t v___x_1185_; size_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1157_, v___x_1185_);
v___x_1187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1154_, v_as_1155_, v_sz_1156_, v___x_1186_, v___x_1184_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1187_;
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_del_object(v___x_1175_);
lean_dec(v_snd_1173_);
v_a_1189_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1179_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1179_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object** _args){
lean_object* v_isLower_1199_ = _args[0];
lean_object* v_as_1200_ = _args[1];
lean_object* v_sz_1201_ = _args[2];
lean_object* v_i_1202_ = _args[3];
lean_object* v_b_1203_ = _args[4];
lean_object* v___y_1204_ = _args[5];
lean_object* v___y_1205_ = _args[6];
lean_object* v___y_1206_ = _args[7];
lean_object* v___y_1207_ = _args[8];
lean_object* v___y_1208_ = _args[9];
lean_object* v___y_1209_ = _args[10];
lean_object* v___y_1210_ = _args[11];
lean_object* v___y_1211_ = _args[12];
lean_object* v___y_1212_ = _args[13];
lean_object* v___y_1213_ = _args[14];
lean_object* v___y_1214_ = _args[15];
lean_object* v___y_1215_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1216_; size_t v_sz_boxed_1217_; size_t v_i_boxed_1218_; lean_object* v_res_1219_; 
v_isLower_boxed_1216_ = lean_unbox(v_isLower_1199_);
v_sz_boxed_1217_ = lean_unbox_usize(v_sz_1201_);
lean_dec(v_sz_1201_);
v_i_boxed_1218_ = lean_unbox_usize(v_i_1202_);
lean_dec(v_i_1202_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1216_, v_as_1200_, v_sz_boxed_1217_, v_i_boxed_1218_, v_b_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v_as_1200_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(uint8_t v_isLower_1220_, lean_object* v_inh_1221_, lean_object* v_n_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
if (lean_obj_tag(v_n_1222_) == 0)
{
lean_object* v_cs_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1270_; 
v_cs_1236_ = lean_ctor_get(v_n_1222_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_n_1222_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1238_ = v_n_1222_;
v_isShared_1239_ = v_isSharedCheck_1270_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_cs_1236_);
lean_dec(v_n_1222_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1270_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; size_t v_sz_1242_; size_t v___x_1243_; lean_object* v___x_1244_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v_b_1223_);
v_sz_1242_ = lean_array_size(v_cs_1236_);
v___x_1243_ = ((size_t)0ULL);
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_isLower_1220_, v_inh_1221_, v_cs_1236_, v_sz_1242_, v___x_1243_, v___x_1241_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec_ref(v_cs_1236_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1261_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1261_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1261_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_fst_1249_; 
v_fst_1249_ = lean_ctor_get(v_a_1245_, 0);
if (lean_obj_tag(v_fst_1249_) == 0)
{
lean_object* v_snd_1250_; lean_object* v___x_1252_; 
v_snd_1250_ = lean_ctor_get(v_a_1245_, 1);
lean_inc(v_snd_1250_);
lean_dec(v_a_1245_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 1);
lean_ctor_set(v___x_1238_, 0, v_snd_1250_);
v___x_1252_ = v___x_1238_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_snd_1250_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1252_);
v___x_1254_ = v___x_1247_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v_val_1257_; lean_object* v___x_1259_; 
lean_inc_ref(v_fst_1249_);
lean_dec(v_a_1245_);
lean_del_object(v___x_1238_);
v_val_1257_ = lean_ctor_get(v_fst_1249_, 0);
lean_inc(v_val_1257_);
lean_dec_ref(v_fst_1249_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v_val_1257_);
v___x_1259_ = v___x_1247_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_val_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_del_object(v___x_1238_);
v_a_1262_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1244_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1244_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
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
}
else
{
lean_object* v_vs_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1305_; 
v_vs_1271_ = lean_ctor_get(v_n_1222_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_n_1222_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1273_ = v_n_1222_;
v_isShared_1274_ = v_isSharedCheck_1305_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_vs_1271_);
lean_dec(v_n_1222_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1305_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; size_t v_sz_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_b_1223_);
v_sz_1277_ = lean_array_size(v_vs_1271_);
v___x_1278_ = ((size_t)0ULL);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1220_, v_vs_1271_, v_sz_1277_, v___x_1278_, v___x_1276_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec_ref(v_vs_1271_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1296_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1296_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1296_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v_fst_1284_; 
v_fst_1284_ = lean_ctor_get(v_a_1280_, 0);
if (lean_obj_tag(v_fst_1284_) == 0)
{
lean_object* v_snd_1285_; lean_object* v___x_1287_; 
v_snd_1285_ = lean_ctor_get(v_a_1280_, 1);
lean_inc(v_snd_1285_);
lean_dec(v_a_1280_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_snd_1285_);
v___x_1287_ = v___x_1273_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_snd_1285_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1287_);
v___x_1289_ = v___x_1282_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_val_1292_; lean_object* v___x_1294_; 
lean_inc_ref(v_fst_1284_);
lean_dec(v_a_1280_);
lean_del_object(v___x_1273_);
v_val_1292_ = lean_ctor_get(v_fst_1284_, 0);
lean_inc(v_val_1292_);
lean_dec_ref(v_fst_1284_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_val_1292_);
v___x_1294_ = v___x_1282_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_val_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_del_object(v___x_1273_);
v_a_1297_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1279_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1279_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(uint8_t v_isLower_1306_, lean_object* v_inh_1307_, lean_object* v_as_1308_, size_t v_sz_1309_, size_t v_i_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_lt(v_i_1310_, v_sz_1309_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_b_1311_);
return v___x_1325_;
}
else
{
lean_object* v_snd_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1360_; 
v_snd_1326_ = lean_ctor_get(v_b_1311_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_b_1311_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v_b_1311_, 0);
lean_dec(v_unused_1361_);
v___x_1328_ = v_b_1311_;
v_isShared_1329_ = v_isSharedCheck_1360_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_snd_1326_);
lean_dec(v_b_1311_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1360_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_a_1330_; lean_object* v___x_1331_; 
v_a_1330_ = lean_array_uget_borrowed(v_as_1308_, v_i_1310_);
lean_inc(v_snd_1326_);
lean_inc(v_a_1330_);
v___x_1331_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_isLower_1306_, v_inh_1307_, v_a_1330_, v_snd_1326_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1351_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1351_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1351_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
if (lean_obj_tag(v_a_1332_) == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_a_1332_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1336_);
v___x_1338_ = v___x_1328_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_snd_1326_);
v___x_1338_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1338_);
v___x_1340_ = v___x_1334_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_del_object(v___x_1334_);
lean_dec(v_snd_1326_);
v_a_1343_ = lean_ctor_get(v_a_1332_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v_a_1332_);
v___x_1344_ = lean_box(0);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v_a_1343_);
lean_ctor_set(v___x_1328_, 0, v___x_1344_);
v___x_1346_ = v___x_1328_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_a_1343_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
size_t v___x_1347_; size_t v___x_1348_; 
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_add(v_i_1310_, v___x_1347_);
v_i_1310_ = v___x_1348_;
v_b_1311_ = v___x_1346_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_del_object(v___x_1328_);
lean_dec(v_snd_1326_);
v_a_1352_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1331_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1331_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_isLower_1362_ = _args[0];
lean_object* v_inh_1363_ = _args[1];
lean_object* v_as_1364_ = _args[2];
lean_object* v_sz_1365_ = _args[3];
lean_object* v_i_1366_ = _args[4];
lean_object* v_b_1367_ = _args[5];
lean_object* v___y_1368_ = _args[6];
lean_object* v___y_1369_ = _args[7];
lean_object* v___y_1370_ = _args[8];
lean_object* v___y_1371_ = _args[9];
lean_object* v___y_1372_ = _args[10];
lean_object* v___y_1373_ = _args[11];
lean_object* v___y_1374_ = _args[12];
lean_object* v___y_1375_ = _args[13];
lean_object* v___y_1376_ = _args[14];
lean_object* v___y_1377_ = _args[15];
lean_object* v___y_1378_ = _args[16];
lean_object* v___y_1379_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_1380_; size_t v_sz_boxed_1381_; size_t v_i_boxed_1382_; lean_object* v_res_1383_; 
v_isLower_boxed_1380_ = lean_unbox(v_isLower_1362_);
v_sz_boxed_1381_ = lean_unbox_usize(v_sz_1365_);
lean_dec(v_sz_1365_);
v_i_boxed_1382_ = lean_unbox_usize(v_i_1366_);
lean_dec(v_i_1366_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_isLower_boxed_1380_, v_inh_1363_, v_as_1364_, v_sz_boxed_1381_, v_i_boxed_1382_, v_b_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v_as_1364_);
lean_dec(v_inh_1363_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_isLower_1384_, lean_object* v_inh_1385_, lean_object* v_n_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v_isLower_boxed_1400_; lean_object* v_res_1401_; 
v_isLower_boxed_1400_ = lean_unbox(v_isLower_1384_);
v_res_1401_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_isLower_boxed_1400_, v_inh_1385_, v_n_1386_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec(v_inh_1385_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1402_, lean_object* v_as_1403_, size_t v_sz_1404_, size_t v_i_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_usize_dec_lt(v_i_1405_, v_sz_1404_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_b_1406_);
return v___x_1420_;
}
else
{
lean_object* v_snd_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1445_; 
v_snd_1421_ = lean_ctor_get(v_b_1406_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_b_1406_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v_b_1406_, 0);
lean_dec(v_unused_1446_);
v___x_1423_ = v_b_1406_;
v_isShared_1424_ = v_isSharedCheck_1445_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_snd_1421_);
lean_dec(v_b_1406_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1445_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_a_1425_ = lean_array_uget_borrowed(v_as_1403_, v_i_1405_);
v___x_1426_ = lean_box(0);
lean_inc(v_a_1425_);
v___x_1427_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1421_, v_isLower_1402_, v_a_1425_, v___x_1426_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_dec_ref(v___x_1427_);
v___x_1428_ = lean_box(0);
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = lean_nat_add(v_snd_1421_, v___x_1429_);
lean_dec(v_snd_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1430_);
lean_ctor_set(v___x_1423_, 0, v___x_1428_);
v___x_1432_ = v___x_1423_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
size_t v___x_1433_; size_t v___x_1434_; 
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1405_, v___x_1433_);
v_i_1405_ = v___x_1434_;
v_b_1406_ = v___x_1432_;
goto _start;
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_del_object(v___x_1423_);
lean_dec(v_snd_1421_);
v_a_1437_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1427_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1427_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object** _args){
lean_object* v_isLower_1447_ = _args[0];
lean_object* v_as_1448_ = _args[1];
lean_object* v_sz_1449_ = _args[2];
lean_object* v_i_1450_ = _args[3];
lean_object* v_b_1451_ = _args[4];
lean_object* v___y_1452_ = _args[5];
lean_object* v___y_1453_ = _args[6];
lean_object* v___y_1454_ = _args[7];
lean_object* v___y_1455_ = _args[8];
lean_object* v___y_1456_ = _args[9];
lean_object* v___y_1457_ = _args[10];
lean_object* v___y_1458_ = _args[11];
lean_object* v___y_1459_ = _args[12];
lean_object* v___y_1460_ = _args[13];
lean_object* v___y_1461_ = _args[14];
lean_object* v___y_1462_ = _args[15];
lean_object* v___y_1463_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1464_; size_t v_sz_boxed_1465_; size_t v_i_boxed_1466_; lean_object* v_res_1467_; 
v_isLower_boxed_1464_ = lean_unbox(v_isLower_1447_);
v_sz_boxed_1465_ = lean_unbox_usize(v_sz_1449_);
lean_dec(v_sz_1449_);
v_i_boxed_1466_ = lean_unbox_usize(v_i_1450_);
lean_dec(v_i_1450_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_1464_, v_as_1448_, v_sz_boxed_1465_, v_i_boxed_1466_, v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v_as_1448_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1468_, lean_object* v_as_1469_, size_t v_sz_1470_, size_t v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_usize_dec_lt(v_i_1471_, v_sz_1470_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1472_);
return v___x_1486_;
}
else
{
lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1511_; 
v_snd_1487_ = lean_ctor_get(v_b_1472_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_b_1472_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v_b_1472_, 0);
lean_dec(v_unused_1512_);
v___x_1489_ = v_b_1472_;
v_isShared_1490_ = v_isSharedCheck_1511_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_dec(v_b_1472_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1511_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_a_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_a_1491_ = lean_array_uget_borrowed(v_as_1469_, v_i_1471_);
v___x_1492_ = lean_box(0);
lean_inc(v_a_1491_);
v___x_1493_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_1487_, v_isLower_1468_, v_a_1491_, v___x_1492_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
lean_dec_ref(v___x_1493_);
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_nat_add(v_snd_1487_, v___x_1495_);
lean_dec(v_snd_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1496_);
lean_ctor_set(v___x_1489_, 0, v___x_1494_);
v___x_1498_ = v___x_1489_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
size_t v___x_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = lean_usize_add(v_i_1471_, v___x_1499_);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1468_, v_as_1469_, v_sz_1470_, v___x_1500_, v___x_1498_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1501_;
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_del_object(v___x_1489_);
lean_dec(v_snd_1487_);
v_a_1503_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1493_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1493_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_isLower_1513_ = _args[0];
lean_object* v_as_1514_ = _args[1];
lean_object* v_sz_1515_ = _args[2];
lean_object* v_i_1516_ = _args[3];
lean_object* v_b_1517_ = _args[4];
lean_object* v___y_1518_ = _args[5];
lean_object* v___y_1519_ = _args[6];
lean_object* v___y_1520_ = _args[7];
lean_object* v___y_1521_ = _args[8];
lean_object* v___y_1522_ = _args[9];
lean_object* v___y_1523_ = _args[10];
lean_object* v___y_1524_ = _args[11];
lean_object* v___y_1525_ = _args[12];
lean_object* v___y_1526_ = _args[13];
lean_object* v___y_1527_ = _args[14];
lean_object* v___y_1528_ = _args[15];
lean_object* v___y_1529_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1530_; size_t v_sz_boxed_1531_; size_t v_i_boxed_1532_; lean_object* v_res_1533_; 
v_isLower_boxed_1530_ = lean_unbox(v_isLower_1513_);
v_sz_boxed_1531_ = lean_unbox_usize(v_sz_1515_);
lean_dec(v_sz_1515_);
v_i_boxed_1532_ = lean_unbox_usize(v_i_1516_);
lean_dec(v_i_1516_);
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1530_, v_as_1514_, v_sz_boxed_1531_, v_i_boxed_1532_, v_b_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v_as_1514_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(uint8_t v_isLower_1534_, lean_object* v_t_1535_, lean_object* v_init_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_root_1549_; lean_object* v_tail_1550_; lean_object* v___x_1551_; 
v_root_1549_ = lean_ctor_get(v_t_1535_, 0);
lean_inc_ref(v_root_1549_);
v_tail_1550_ = lean_ctor_get(v_t_1535_, 1);
lean_inc_ref(v_tail_1550_);
lean_dec_ref(v_t_1535_);
lean_inc(v_init_1536_);
v___x_1551_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_isLower_1534_, v_init_1536_, v_root_1549_, v_init_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v_init_1536_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1588_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1588_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1588_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
if (lean_obj_tag(v_a_1552_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; 
lean_dec_ref(v_tail_1550_);
v_a_1556_ = lean_ctor_get(v_a_1552_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v_a_1552_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v_a_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; size_t v_sz_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
lean_del_object(v___x_1554_);
v_a_1560_ = lean_ctor_get(v_a_1552_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v_a_1552_);
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v_a_1560_);
v_sz_1563_ = lean_array_size(v_tail_1550_);
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_1534_, v_tail_1550_, v_sz_1563_, v___x_1564_, v___x_1562_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v_tail_1550_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1579_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_fst_1570_; 
v_fst_1570_ = lean_ctor_get(v_a_1566_, 0);
if (lean_obj_tag(v_fst_1570_) == 0)
{
lean_object* v_snd_1571_; lean_object* v___x_1573_; 
v_snd_1571_ = lean_ctor_get(v_a_1566_, 1);
lean_inc(v_snd_1571_);
lean_dec(v_a_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_snd_1571_);
v___x_1573_ = v___x_1568_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_snd_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v_val_1575_; lean_object* v___x_1577_; 
lean_inc_ref(v_fst_1570_);
lean_dec(v_a_1566_);
v_val_1575_ = lean_ctor_get(v_fst_1570_, 0);
lean_inc(v_val_1575_);
lean_dec_ref(v_fst_1570_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_val_1575_);
v___x_1577_ = v___x_1568_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_val_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_a_1580_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1565_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1565_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_tail_1550_);
v_a_1589_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1551_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1551_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1597_, lean_object* v_t_1598_, lean_object* v_init_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
uint8_t v_isLower_boxed_1612_; lean_object* v_res_1613_; 
v_isLower_boxed_1612_ = lean_unbox(v_isLower_1597_);
v_res_1613_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_boxed_1612_, v_t_1598_, v_init_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec(v___y_1600_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(lean_object* v_css_1614_, uint8_t v_isLower_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_x_1628_; lean_object* v___x_1629_; 
v_x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_1615_, v_css_1614_, v_x_1628_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1637_; 
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v___x_1629_, 0);
lean_dec(v_unused_1638_);
v___x_1631_ = v___x_1629_;
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
else
{
lean_dec(v___x_1629_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_a_1639_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1629_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1629_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs___boxed(lean_object* v_css_1647_, lean_object* v_isLower_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
uint8_t v_isLower_boxed_1661_; lean_object* v_res_1662_; 
v_isLower_boxed_1661_ = lean_unbox(v_isLower_1648_);
v_res_1662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_css_1647_, v_isLower_boxed_1661_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
return v_res_1662_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1));
v___x_1666_ = lean_unsigned_to_nat(2u);
v___x_1667_ = lean_unsigned_to_nat(63u);
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0));
v___x_1669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_1670_ = l_mkPanicMessageWithDecl(v___x_1669_, v___x_1668_, v___x_1667_, v___x_1666_, v___x_1665_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v_lowers_1685_; lean_object* v_vars_1686_; lean_object* v_size_1687_; lean_object* v_size_1688_; uint8_t v___x_1689_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v_lowers_1685_ = lean_ctor_get(v_a_1684_, 32);
lean_inc_ref(v_lowers_1685_);
v_vars_1686_ = lean_ctor_get(v_a_1684_, 30);
lean_inc_ref(v_vars_1686_);
lean_dec(v_a_1684_);
v_size_1687_ = lean_ctor_get(v_lowers_1685_, 2);
v_size_1688_ = lean_ctor_get(v_vars_1686_, 2);
lean_inc(v_size_1688_);
lean_dec_ref(v_vars_1686_);
v___x_1689_ = lean_nat_dec_eq(v_size_1687_, v_size_1688_);
lean_dec(v_size_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec_ref(v_lowers_1685_);
v___x_1690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2);
v___x_1691_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_1690_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; 
v___x_1692_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_lowers_1685_, v___x_1689_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1692_;
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1683_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1683_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___boxed(lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec(v_a_1701_);
return v_res_1713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1));
v___x_1717_ = lean_unsigned_to_nat(2u);
v___x_1718_ = lean_unsigned_to_nat(68u);
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0));
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_1721_ = l_mkPanicMessageWithDecl(v___x_1720_, v___x_1719_, v___x_1718_, v___x_1717_, v___x_1716_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v_uppers_1736_; lean_object* v_vars_1737_; lean_object* v_size_1738_; lean_object* v_size_1739_; uint8_t v___x_1740_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
v_uppers_1736_ = lean_ctor_get(v_a_1735_, 33);
lean_inc_ref(v_uppers_1736_);
v_vars_1737_ = lean_ctor_get(v_a_1735_, 30);
lean_inc_ref(v_vars_1737_);
lean_dec(v_a_1735_);
v_size_1738_ = lean_ctor_get(v_uppers_1736_, 2);
v_size_1739_ = lean_ctor_get(v_vars_1737_, 2);
lean_inc(v_size_1739_);
lean_dec_ref(v_vars_1737_);
v___x_1740_ = lean_nat_dec_eq(v_size_1738_, v_size_1739_);
lean_dec(v_size_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec_ref(v_uppers_1736_);
v___x_1741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2);
v___x_1742_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_1741_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = 0;
v___x_1744_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_uppers_1736_, v___x_1743_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1744_;
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1734_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1734_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___boxed(lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec(v_a_1753_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_1769_, lean_object* v_as_1770_, size_t v_sz_1771_, size_t v_i_1772_, lean_object* v_b_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
uint8_t v___x_1786_; 
v___x_1786_ = lean_usize_dec_lt(v_i_1772_, v_sz_1771_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_b_1773_);
return v___x_1787_;
}
else
{
lean_object* v_a_1788_; lean_object* v_p_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v_b_1773_);
v_a_1788_ = lean_array_uget_borrowed(v_as_1770_, v_i_1772_);
v_p_1789_ = lean_ctor_get(v_a_1788_, 0);
v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_1789_, v_____s_1769_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1791_; size_t v___x_1792_; size_t v___x_1793_; 
lean_dec_ref(v___x_1790_);
v___x_1791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = lean_usize_add(v_i_1772_, v___x_1792_);
v_i_1772_ = v___x_1793_;
v_b_1773_ = v___x_1791_;
goto _start;
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_a_1795_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1790_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1790_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_____s_1803_ = _args[0];
lean_object* v_as_1804_ = _args[1];
lean_object* v_sz_1805_ = _args[2];
lean_object* v_i_1806_ = _args[3];
lean_object* v_b_1807_ = _args[4];
lean_object* v___y_1808_ = _args[5];
lean_object* v___y_1809_ = _args[6];
lean_object* v___y_1810_ = _args[7];
lean_object* v___y_1811_ = _args[8];
lean_object* v___y_1812_ = _args[9];
lean_object* v___y_1813_ = _args[10];
lean_object* v___y_1814_ = _args[11];
lean_object* v___y_1815_ = _args[12];
lean_object* v___y_1816_ = _args[13];
lean_object* v___y_1817_ = _args[14];
lean_object* v___y_1818_ = _args[15];
lean_object* v___y_1819_ = _args[16];
_start:
{
size_t v_sz_boxed_1820_; size_t v_i_boxed_1821_; lean_object* v_res_1822_; 
v_sz_boxed_1820_ = lean_unbox_usize(v_sz_1805_);
lean_dec(v_sz_1805_);
v_i_boxed_1821_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_res_1822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_1803_, v_as_1804_, v_sz_boxed_1820_, v_i_boxed_1821_, v_b_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v_as_1804_);
lean_dec(v_____s_1803_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_1823_, lean_object* v_as_1824_, size_t v_sz_1825_, size_t v_i_1826_, lean_object* v_b_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = lean_usize_dec_lt(v_i_1826_, v_sz_1825_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_b_1827_);
return v___x_1841_;
}
else
{
lean_object* v_a_1842_; lean_object* v_p_1843_; lean_object* v___x_1844_; 
lean_dec_ref(v_b_1827_);
v_a_1842_ = lean_array_uget_borrowed(v_as_1824_, v_i_1826_);
v_p_1843_ = lean_ctor_get(v_a_1842_, 0);
v___x_1844_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_1843_, v_____s_1823_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v___x_1845_; size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; 
lean_dec_ref(v___x_1844_);
v___x_1845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_add(v_i_1826_, v___x_1846_);
v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_1823_, v_as_1824_, v_sz_1825_, v___x_1847_, v___x_1845_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_1848_;
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1844_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1844_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_____s_1857_ = _args[0];
lean_object* v_as_1858_ = _args[1];
lean_object* v_sz_1859_ = _args[2];
lean_object* v_i_1860_ = _args[3];
lean_object* v_b_1861_ = _args[4];
lean_object* v___y_1862_ = _args[5];
lean_object* v___y_1863_ = _args[6];
lean_object* v___y_1864_ = _args[7];
lean_object* v___y_1865_ = _args[8];
lean_object* v___y_1866_ = _args[9];
lean_object* v___y_1867_ = _args[10];
lean_object* v___y_1868_ = _args[11];
lean_object* v___y_1869_ = _args[12];
lean_object* v___y_1870_ = _args[13];
lean_object* v___y_1871_ = _args[14];
lean_object* v___y_1872_ = _args[15];
lean_object* v___y_1873_ = _args[16];
_start:
{
size_t v_sz_boxed_1874_; size_t v_i_boxed_1875_; lean_object* v_res_1876_; 
v_sz_boxed_1874_ = lean_unbox_usize(v_sz_1859_);
lean_dec(v_sz_1859_);
v_i_boxed_1875_ = lean_unbox_usize(v_i_1860_);
lean_dec(v_i_1860_);
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_1857_, v_as_1858_, v_sz_boxed_1874_, v_i_boxed_1875_, v_b_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v_as_1858_);
lean_dec(v_____s_1857_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_____s_1877_, lean_object* v_inh_1878_, lean_object* v_n_1879_, lean_object* v_b_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
if (lean_obj_tag(v_n_1879_) == 0)
{
lean_object* v_cs_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1927_; 
v_cs_1893_ = lean_ctor_get(v_n_1879_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_n_1879_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1895_ = v_n_1879_;
v_isShared_1896_ = v_isSharedCheck_1927_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_cs_1893_);
lean_dec(v_n_1879_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1927_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; size_t v_sz_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v_b_1880_);
v_sz_1899_ = lean_array_size(v_cs_1893_);
v___x_1900_ = ((size_t)0ULL);
v___x_1901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_____s_1877_, v_inh_1878_, v_cs_1893_, v_sz_1899_, v___x_1900_, v___x_1898_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec_ref(v_cs_1893_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1918_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1918_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1918_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v_fst_1906_; 
v_fst_1906_ = lean_ctor_get(v_a_1902_, 0);
if (lean_obj_tag(v_fst_1906_) == 0)
{
lean_object* v_snd_1907_; lean_object* v___x_1909_; 
v_snd_1907_ = lean_ctor_get(v_a_1902_, 1);
lean_inc(v_snd_1907_);
lean_dec(v_a_1902_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
lean_ctor_set(v___x_1895_, 0, v_snd_1907_);
v___x_1909_ = v___x_1895_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_snd_1907_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1909_);
v___x_1911_ = v___x_1904_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_object* v_val_1914_; lean_object* v___x_1916_; 
lean_inc_ref(v_fst_1906_);
lean_dec(v_a_1902_);
lean_del_object(v___x_1895_);
v_val_1914_ = lean_ctor_get(v_fst_1906_, 0);
lean_inc(v_val_1914_);
lean_dec_ref(v_fst_1906_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_val_1914_);
v___x_1916_ = v___x_1904_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_val_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_del_object(v___x_1895_);
v_a_1919_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1901_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1901_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
else
{
lean_object* v_vs_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1962_; 
v_vs_1928_ = lean_ctor_get(v_n_1879_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_n_1879_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1930_ = v_n_1879_;
v_isShared_1931_ = v_isSharedCheck_1962_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_vs_1928_);
lean_dec(v_n_1879_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1962_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v_b_1880_);
v_sz_1934_ = lean_array_size(v_vs_1928_);
v___x_1935_ = ((size_t)0ULL);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_1877_, v_vs_1928_, v_sz_1934_, v___x_1935_, v___x_1933_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec_ref(v_vs_1928_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1953_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1953_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1953_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_fst_1941_; 
v_fst_1941_ = lean_ctor_get(v_a_1937_, 0);
if (lean_obj_tag(v_fst_1941_) == 0)
{
lean_object* v_snd_1942_; lean_object* v___x_1944_; 
v_snd_1942_ = lean_ctor_get(v_a_1937_, 1);
lean_inc(v_snd_1942_);
lean_dec(v_a_1937_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v_snd_1942_);
v___x_1944_ = v___x_1930_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_snd_1942_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1944_);
v___x_1946_ = v___x_1939_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
else
{
lean_object* v_val_1949_; lean_object* v___x_1951_; 
lean_inc_ref(v_fst_1941_);
lean_dec(v_a_1937_);
lean_del_object(v___x_1930_);
v_val_1949_ = lean_ctor_get(v_fst_1941_, 0);
lean_inc(v_val_1949_);
lean_dec_ref(v_fst_1941_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v_val_1949_);
v___x_1951_ = v___x_1939_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_val_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_del_object(v___x_1930_);
v_a_1954_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1936_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1936_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_____s_1963_, lean_object* v_inh_1964_, lean_object* v_as_1965_, size_t v_sz_1966_, size_t v_i_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_usize_dec_lt(v_i_1967_, v_sz_1966_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_b_1968_);
return v___x_1982_;
}
else
{
lean_object* v_snd_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2017_; 
v_snd_1983_ = lean_ctor_get(v_b_1968_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_b_1968_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v_b_1968_, 0);
lean_dec(v_unused_2018_);
v___x_1985_ = v_b_1968_;
v_isShared_1986_ = v_isSharedCheck_2017_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snd_1983_);
lean_dec(v_b_1968_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2017_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_a_1987_ = lean_array_uget_borrowed(v_as_1965_, v_i_1967_);
lean_inc(v_snd_1983_);
lean_inc(v_a_1987_);
v___x_1988_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_____s_1963_, v_inh_1964_, v_a_1987_, v_snd_1983_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2008_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2008_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2008_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
if (lean_obj_tag(v_a_1989_) == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_a_1989_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1993_);
v___x_1995_ = v___x_1985_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_snd_1983_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1995_);
v___x_1997_ = v___x_1991_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
lean_del_object(v___x_1991_);
lean_dec(v_snd_1983_);
v_a_2000_ = lean_ctor_get(v_a_1989_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v_a_1989_);
v___x_2001_ = lean_box(0);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v_a_2000_);
lean_ctor_set(v___x_1985_, 0, v___x_2001_);
v___x_2003_ = v___x_1985_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_a_2000_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
size_t v___x_2004_; size_t v___x_2005_; 
v___x_2004_ = ((size_t)1ULL);
v___x_2005_ = lean_usize_add(v_i_1967_, v___x_2004_);
v_i_1967_ = v___x_2005_;
v_b_1968_ = v___x_2003_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
v_a_2009_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1988_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1988_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_____s_2019_ = _args[0];
lean_object* v_inh_2020_ = _args[1];
lean_object* v_as_2021_ = _args[2];
lean_object* v_sz_2022_ = _args[3];
lean_object* v_i_2023_ = _args[4];
lean_object* v_b_2024_ = _args[5];
lean_object* v___y_2025_ = _args[6];
lean_object* v___y_2026_ = _args[7];
lean_object* v___y_2027_ = _args[8];
lean_object* v___y_2028_ = _args[9];
lean_object* v___y_2029_ = _args[10];
lean_object* v___y_2030_ = _args[11];
lean_object* v___y_2031_ = _args[12];
lean_object* v___y_2032_ = _args[13];
lean_object* v___y_2033_ = _args[14];
lean_object* v___y_2034_ = _args[15];
lean_object* v___y_2035_ = _args[16];
lean_object* v___y_2036_ = _args[17];
_start:
{
size_t v_sz_boxed_2037_; size_t v_i_boxed_2038_; lean_object* v_res_2039_; 
v_sz_boxed_2037_ = lean_unbox_usize(v_sz_2022_);
lean_dec(v_sz_2022_);
v_i_boxed_2038_ = lean_unbox_usize(v_i_2023_);
lean_dec(v_i_2023_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_____s_2019_, v_inh_2020_, v_as_2021_, v_sz_boxed_2037_, v_i_boxed_2038_, v_b_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v_as_2021_);
lean_dec(v_____s_2019_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_____s_2040_, lean_object* v_inh_2041_, lean_object* v_n_2042_, lean_object* v_b_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_____s_2040_, v_inh_2041_, v_n_2042_, v_b_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec(v_____s_2040_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_2060_, lean_object* v_as_2061_, size_t v_sz_2062_, size_t v_i_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_usize_dec_lt(v_i_2063_, v_sz_2062_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_b_2064_);
return v___x_2078_;
}
else
{
lean_object* v_a_2079_; lean_object* v_p_2080_; lean_object* v___x_2081_; 
lean_dec_ref(v_b_2064_);
v_a_2079_ = lean_array_uget_borrowed(v_as_2061_, v_i_2063_);
v_p_2080_ = lean_ctor_get(v_a_2079_, 0);
v___x_2081_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_2080_, v_____s_2060_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; 
lean_dec_ref(v___x_2081_);
v___x_2082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_add(v_i_2063_, v___x_2083_);
v_i_2063_ = v___x_2084_;
v_b_2064_ = v___x_2082_;
goto _start;
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
v_a_2086_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2081_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2081_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_____s_2094_ = _args[0];
lean_object* v_as_2095_ = _args[1];
lean_object* v_sz_2096_ = _args[2];
lean_object* v_i_2097_ = _args[3];
lean_object* v_b_2098_ = _args[4];
lean_object* v___y_2099_ = _args[5];
lean_object* v___y_2100_ = _args[6];
lean_object* v___y_2101_ = _args[7];
lean_object* v___y_2102_ = _args[8];
lean_object* v___y_2103_ = _args[9];
lean_object* v___y_2104_ = _args[10];
lean_object* v___y_2105_ = _args[11];
lean_object* v___y_2106_ = _args[12];
lean_object* v___y_2107_ = _args[13];
lean_object* v___y_2108_ = _args[14];
lean_object* v___y_2109_ = _args[15];
lean_object* v___y_2110_ = _args[16];
_start:
{
size_t v_sz_boxed_2111_; size_t v_i_boxed_2112_; lean_object* v_res_2113_; 
v_sz_boxed_2111_ = lean_unbox_usize(v_sz_2096_);
lean_dec(v_sz_2096_);
v_i_boxed_2112_ = lean_unbox_usize(v_i_2097_);
lean_dec(v_i_2097_);
v_res_2113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_2094_, v_as_2095_, v_sz_boxed_2111_, v_i_boxed_2112_, v_b_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v_as_2095_);
lean_dec(v_____s_2094_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_2114_, lean_object* v_as_2115_, size_t v_sz_2116_, size_t v_i_2117_, lean_object* v_b_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v___x_2131_; 
v___x_2131_ = lean_usize_dec_lt(v_i_2117_, v_sz_2116_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_b_2118_);
return v___x_2132_;
}
else
{
lean_object* v_a_2133_; lean_object* v_p_2134_; lean_object* v___x_2135_; 
lean_dec_ref(v_b_2118_);
v_a_2133_ = lean_array_uget_borrowed(v_as_2115_, v_i_2117_);
v_p_2134_ = lean_ctor_get(v_a_2133_, 0);
v___x_2135_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_2134_, v_____s_2114_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2136_; size_t v___x_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
lean_dec_ref(v___x_2135_);
v___x_2136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_2137_ = ((size_t)1ULL);
v___x_2138_ = lean_usize_add(v_i_2117_, v___x_2137_);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_2114_, v_as_2115_, v_sz_2116_, v___x_2138_, v___x_2136_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
return v___x_2139_;
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_a_2140_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2135_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2135_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_____s_2148_ = _args[0];
lean_object* v_as_2149_ = _args[1];
lean_object* v_sz_2150_ = _args[2];
lean_object* v_i_2151_ = _args[3];
lean_object* v_b_2152_ = _args[4];
lean_object* v___y_2153_ = _args[5];
lean_object* v___y_2154_ = _args[6];
lean_object* v___y_2155_ = _args[7];
lean_object* v___y_2156_ = _args[8];
lean_object* v___y_2157_ = _args[9];
lean_object* v___y_2158_ = _args[10];
lean_object* v___y_2159_ = _args[11];
lean_object* v___y_2160_ = _args[12];
lean_object* v___y_2161_ = _args[13];
lean_object* v___y_2162_ = _args[14];
lean_object* v___y_2163_ = _args[15];
lean_object* v___y_2164_ = _args[16];
_start:
{
size_t v_sz_boxed_2165_; size_t v_i_boxed_2166_; lean_object* v_res_2167_; 
v_sz_boxed_2165_ = lean_unbox_usize(v_sz_2150_);
lean_dec(v_sz_2150_);
v_i_boxed_2166_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_res_2167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_2148_, v_as_2149_, v_sz_boxed_2165_, v_i_boxed_2166_, v_b_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v_as_2149_);
lean_dec(v_____s_2148_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(lean_object* v_____s_2168_, lean_object* v_t_2169_, lean_object* v_init_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_root_2183_; lean_object* v_tail_2184_; lean_object* v___x_2185_; 
v_root_2183_ = lean_ctor_get(v_t_2169_, 0);
lean_inc_ref(v_root_2183_);
v_tail_2184_ = lean_ctor_get(v_t_2169_, 1);
lean_inc_ref(v_tail_2184_);
lean_dec_ref(v_t_2169_);
v___x_2185_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_____s_2168_, v_init_2170_, v_root_2183_, v_init_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2222_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2222_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2222_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
if (lean_obj_tag(v_a_2186_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; 
lean_dec_ref(v_tail_2184_);
v_a_2190_ = lean_ctor_get(v_a_2186_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v_a_2186_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v_a_2190_);
v___x_2192_ = v___x_2188_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_2199_; 
lean_del_object(v___x_2188_);
v_a_2194_ = lean_ctor_get(v_a_2186_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v_a_2186_);
v___x_2195_ = lean_box(0);
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v_a_2194_);
v_sz_2197_ = lean_array_size(v_tail_2184_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_2168_, v_tail_2184_, v_sz_2197_, v___x_2198_, v___x_2196_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec_ref(v_tail_2184_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2213_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2213_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2213_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_fst_2204_; 
v_fst_2204_ = lean_ctor_get(v_a_2200_, 0);
if (lean_obj_tag(v_fst_2204_) == 0)
{
lean_object* v_snd_2205_; lean_object* v___x_2207_; 
v_snd_2205_ = lean_ctor_get(v_a_2200_, 1);
lean_inc(v_snd_2205_);
lean_dec(v_a_2200_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_snd_2205_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_snd_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2211_; 
lean_inc_ref(v_fst_2204_);
lean_dec(v_a_2200_);
v_val_2209_ = lean_ctor_get(v_fst_2204_, 0);
lean_inc(v_val_2209_);
lean_dec_ref(v_fst_2204_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_val_2209_);
v___x_2211_ = v___x_2202_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_val_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_a_2214_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2199_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2199_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_tail_2184_);
v_a_2223_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2185_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2185_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_2231_, lean_object* v_t_2232_, lean_object* v_init_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_____s_2231_, v_t_2232_, v_init_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec(v_____s_2231_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_2247_, size_t v_sz_2248_, size_t v_i_2249_, lean_object* v_b_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
uint8_t v___x_2263_; 
v___x_2263_ = lean_usize_dec_lt(v_i_2249_, v_sz_2248_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v_b_2250_);
return v___x_2264_;
}
else
{
lean_object* v_snd_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2289_; 
v_snd_2265_ = lean_ctor_get(v_b_2250_, 1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_b_2250_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v_b_2250_, 0);
lean_dec(v_unused_2290_);
v___x_2267_ = v_b_2250_;
v_isShared_2268_ = v_isSharedCheck_2289_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_snd_2265_);
lean_dec(v_b_2250_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2289_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_a_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_a_2269_ = lean_array_uget_borrowed(v_as_2247_, v_i_2249_);
v___x_2270_ = lean_box(0);
lean_inc(v_a_2269_);
v___x_2271_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2265_, v_a_2269_, v___x_2270_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
lean_dec_ref(v___x_2271_);
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_unsigned_to_nat(1u);
v___x_2274_ = lean_nat_add(v_snd_2265_, v___x_2273_);
lean_dec(v_snd_2265_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2274_);
lean_ctor_set(v___x_2267_, 0, v___x_2272_);
v___x_2276_ = v___x_2267_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
size_t v___x_2277_; size_t v___x_2278_; 
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_add(v_i_2249_, v___x_2277_);
v_i_2249_ = v___x_2278_;
v_b_2250_ = v___x_2276_;
goto _start;
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_del_object(v___x_2267_);
lean_dec(v_snd_2265_);
v_a_2281_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2271_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2271_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_2291_, lean_object* v_sz_2292_, lean_object* v_i_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
size_t v_sz_boxed_2307_; size_t v_i_boxed_2308_; lean_object* v_res_2309_; 
v_sz_boxed_2307_ = lean_unbox_usize(v_sz_2292_);
lean_dec(v_sz_2292_);
v_i_boxed_2308_ = lean_unbox_usize(v_i_2293_);
lean_dec(v_i_2293_);
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_2291_, v_sz_boxed_2307_, v_i_boxed_2308_, v_b_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v_as_2291_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_2310_, size_t v_sz_2311_, size_t v_i_2312_, lean_object* v_b_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_usize_dec_lt(v_i_2312_, v_sz_2311_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_b_2313_);
return v___x_2327_;
}
else
{
lean_object* v_snd_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2352_; 
v_snd_2328_ = lean_ctor_get(v_b_2313_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_b_2313_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v_b_2313_, 0);
lean_dec(v_unused_2353_);
v___x_2330_ = v_b_2313_;
v_isShared_2331_ = v_isSharedCheck_2352_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_snd_2328_);
lean_dec(v_b_2313_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2352_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2332_ = lean_array_uget_borrowed(v_as_2310_, v_i_2312_);
v___x_2333_ = lean_box(0);
lean_inc(v_a_2332_);
v___x_2334_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2328_, v_a_2332_, v___x_2333_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
lean_dec_ref(v___x_2334_);
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = lean_nat_add(v_snd_2328_, v___x_2336_);
lean_dec(v_snd_2328_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 1, v___x_2337_);
lean_ctor_set(v___x_2330_, 0, v___x_2335_);
v___x_2339_ = v___x_2330_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
size_t v___x_2340_; size_t v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = ((size_t)1ULL);
v___x_2341_ = lean_usize_add(v_i_2312_, v___x_2340_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_2310_, v_sz_2311_, v___x_2341_, v___x_2339_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
return v___x_2342_;
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_del_object(v___x_2330_);
lean_dec(v_snd_2328_);
v_a_2344_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2334_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2334_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_2354_, lean_object* v_sz_2355_, lean_object* v_i_2356_, lean_object* v_b_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
size_t v_sz_boxed_2370_; size_t v_i_boxed_2371_; lean_object* v_res_2372_; 
v_sz_boxed_2370_ = lean_unbox_usize(v_sz_2355_);
lean_dec(v_sz_2355_);
v_i_boxed_2371_ = lean_unbox_usize(v_i_2356_);
lean_dec(v_i_2356_);
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_as_2354_, v_sz_boxed_2370_, v_i_boxed_2371_, v_b_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v_as_2354_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_2373_, size_t v_sz_2374_, size_t v_i_2375_, lean_object* v_b_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v___x_2389_; 
v___x_2389_ = lean_usize_dec_lt(v_i_2375_, v_sz_2374_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v_b_2376_);
return v___x_2390_;
}
else
{
lean_object* v_snd_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2415_; 
v_snd_2391_ = lean_ctor_get(v_b_2376_, 1);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_b_2376_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v_b_2376_, 0);
lean_dec(v_unused_2416_);
v___x_2393_ = v_b_2376_;
v_isShared_2394_ = v_isSharedCheck_2415_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_snd_2391_);
lean_dec(v_b_2376_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2415_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_a_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_a_2395_ = lean_array_uget_borrowed(v_as_2373_, v_i_2375_);
v___x_2396_ = lean_box(0);
lean_inc(v_a_2395_);
v___x_2397_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2391_, v_a_2395_, v___x_2396_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
lean_dec_ref(v___x_2397_);
v___x_2398_ = lean_box(0);
v___x_2399_ = lean_unsigned_to_nat(1u);
v___x_2400_ = lean_nat_add(v_snd_2391_, v___x_2399_);
lean_dec(v_snd_2391_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2400_);
lean_ctor_set(v___x_2393_, 0, v___x_2398_);
v___x_2402_ = v___x_2393_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
size_t v___x_2403_; size_t v___x_2404_; 
v___x_2403_ = ((size_t)1ULL);
v___x_2404_ = lean_usize_add(v_i_2375_, v___x_2403_);
v_i_2375_ = v___x_2404_;
v_b_2376_ = v___x_2402_;
goto _start;
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_del_object(v___x_2393_);
lean_dec(v_snd_2391_);
v_a_2407_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2397_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2397_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_2417_, lean_object* v_sz_2418_, lean_object* v_i_2419_, lean_object* v_b_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
size_t v_sz_boxed_2433_; size_t v_i_boxed_2434_; lean_object* v_res_2435_; 
v_sz_boxed_2433_ = lean_unbox_usize(v_sz_2418_);
lean_dec(v_sz_2418_);
v_i_boxed_2434_ = lean_unbox_usize(v_i_2419_);
lean_dec(v_i_2419_);
v_res_2435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_2417_, v_sz_boxed_2433_, v_i_boxed_2434_, v_b_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v_as_2417_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_2436_, size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
uint8_t v___x_2452_; 
v___x_2452_ = lean_usize_dec_lt(v_i_2438_, v_sz_2437_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_b_2439_);
return v___x_2453_;
}
else
{
lean_object* v_snd_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2478_; 
v_snd_2454_ = lean_ctor_get(v_b_2439_, 1);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_b_2439_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v_b_2439_, 0);
lean_dec(v_unused_2479_);
v___x_2456_ = v_b_2439_;
v_isShared_2457_ = v_isSharedCheck_2478_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_snd_2454_);
lean_dec(v_b_2439_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2478_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_a_2458_ = lean_array_uget_borrowed(v_as_2436_, v_i_2438_);
v___x_2459_ = lean_box(0);
lean_inc(v_a_2458_);
v___x_2460_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_2454_, v_a_2458_, v___x_2459_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_dec_ref(v___x_2460_);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_unsigned_to_nat(1u);
v___x_2463_ = lean_nat_add(v_snd_2454_, v___x_2462_);
lean_dec(v_snd_2454_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 1, v___x_2463_);
lean_ctor_set(v___x_2456_, 0, v___x_2461_);
v___x_2465_ = v___x_2456_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = ((size_t)1ULL);
v___x_2467_ = lean_usize_add(v_i_2438_, v___x_2466_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_2436_, v_sz_2437_, v___x_2467_, v___x_2465_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
return v___x_2468_;
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_del_object(v___x_2456_);
lean_dec(v_snd_2454_);
v_a_2470_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2460_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2460_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_2480_, lean_object* v_sz_2481_, lean_object* v_i_2482_, lean_object* v_b_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
size_t v_sz_boxed_2496_; size_t v_i_boxed_2497_; lean_object* v_res_2498_; 
v_sz_boxed_2496_ = lean_unbox_usize(v_sz_2481_);
lean_dec(v_sz_2481_);
v_i_boxed_2497_ = lean_unbox_usize(v_i_2482_);
lean_dec(v_i_2482_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_2480_, v_sz_boxed_2496_, v_i_boxed_2497_, v_b_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v_as_2480_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_inh_2499_, lean_object* v_n_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
if (lean_obj_tag(v_n_2500_) == 0)
{
lean_object* v_cs_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2548_; 
v_cs_2514_ = lean_ctor_get(v_n_2500_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_n_2500_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2516_ = v_n_2500_;
v_isShared_2517_ = v_isSharedCheck_2548_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_cs_2514_);
lean_dec(v_n_2500_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2548_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; size_t v_sz_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v_b_2501_);
v_sz_2520_ = lean_array_size(v_cs_2514_);
v___x_2521_ = ((size_t)0ULL);
v___x_2522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_inh_2499_, v_cs_2514_, v_sz_2520_, v___x_2521_, v___x_2519_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec_ref(v_cs_2514_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2539_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2539_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2539_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_fst_2527_; 
v_fst_2527_ = lean_ctor_get(v_a_2523_, 0);
if (lean_obj_tag(v_fst_2527_) == 0)
{
lean_object* v_snd_2528_; lean_object* v___x_2530_; 
v_snd_2528_ = lean_ctor_get(v_a_2523_, 1);
lean_inc(v_snd_2528_);
lean_dec(v_a_2523_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 1);
lean_ctor_set(v___x_2516_, 0, v_snd_2528_);
v___x_2530_ = v___x_2516_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_snd_2528_);
v___x_2530_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2532_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2530_);
v___x_2532_ = v___x_2525_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_object* v_val_2535_; lean_object* v___x_2537_; 
lean_inc_ref(v_fst_2527_);
lean_dec(v_a_2523_);
lean_del_object(v___x_2516_);
v_val_2535_ = lean_ctor_get(v_fst_2527_, 0);
lean_inc(v_val_2535_);
lean_dec_ref(v_fst_2527_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_val_2535_);
v___x_2537_ = v___x_2525_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_val_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2516_);
v_a_2540_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2522_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2522_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
else
{
lean_object* v_vs_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2583_; 
v_vs_2549_ = lean_ctor_get(v_n_2500_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_n_2500_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2551_ = v_n_2500_;
v_isShared_2552_ = v_isSharedCheck_2583_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_vs_2549_);
lean_dec(v_n_2500_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2583_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; size_t v_sz_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v___x_2553_ = lean_box(0);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v_b_2501_);
v_sz_2555_ = lean_array_size(v_vs_2549_);
v___x_2556_ = ((size_t)0ULL);
v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_2549_, v_sz_2555_, v___x_2556_, v___x_2554_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec_ref(v_vs_2549_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2574_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2574_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2574_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_fst_2562_; 
v_fst_2562_ = lean_ctor_get(v_a_2558_, 0);
if (lean_obj_tag(v_fst_2562_) == 0)
{
lean_object* v_snd_2563_; lean_object* v___x_2565_; 
v_snd_2563_ = lean_ctor_get(v_a_2558_, 1);
lean_inc(v_snd_2563_);
lean_dec(v_a_2558_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_snd_2563_);
v___x_2565_ = v___x_2551_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_snd_2563_);
v___x_2565_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2567_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2565_);
v___x_2567_ = v___x_2560_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v_val_2570_; lean_object* v___x_2572_; 
lean_inc_ref(v_fst_2562_);
lean_dec(v_a_2558_);
lean_del_object(v___x_2551_);
v_val_2570_ = lean_ctor_get(v_fst_2562_, 0);
lean_inc(v_val_2570_);
lean_dec_ref(v_fst_2562_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_val_2570_);
v___x_2572_ = v___x_2560_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_val_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_del_object(v___x_2551_);
v_a_2575_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2557_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2557_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_inh_2584_, lean_object* v_as_2585_, size_t v_sz_2586_, size_t v_i_2587_, lean_object* v_b_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
uint8_t v___x_2601_; 
v___x_2601_ = lean_usize_dec_lt(v_i_2587_, v_sz_2586_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v_b_2588_);
return v___x_2602_;
}
else
{
lean_object* v_snd_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2637_; 
v_snd_2603_ = lean_ctor_get(v_b_2588_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_b_2588_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v_b_2588_, 0);
lean_dec(v_unused_2638_);
v___x_2605_ = v_b_2588_;
v_isShared_2606_ = v_isSharedCheck_2637_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_snd_2603_);
lean_dec(v_b_2588_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2637_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v_a_2607_; lean_object* v___x_2608_; 
v_a_2607_ = lean_array_uget_borrowed(v_as_2585_, v_i_2587_);
lean_inc(v_snd_2603_);
lean_inc(v_a_2607_);
v___x_2608_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_inh_2584_, v_a_2607_, v_snd_2603_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2628_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2628_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2628_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
if (lean_obj_tag(v_a_2609_) == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_a_2609_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2613_);
v___x_2615_ = v___x_2605_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_snd_2603_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2615_);
v___x_2617_ = v___x_2611_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_del_object(v___x_2611_);
lean_dec(v_snd_2603_);
v_a_2620_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_a_2620_);
lean_dec_ref(v_a_2609_);
v___x_2621_ = lean_box(0);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 1, v_a_2620_);
lean_ctor_set(v___x_2605_, 0, v___x_2621_);
v___x_2623_ = v___x_2605_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_a_2620_);
v___x_2623_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
size_t v___x_2624_; size_t v___x_2625_; 
v___x_2624_ = ((size_t)1ULL);
v___x_2625_ = lean_usize_add(v_i_2587_, v___x_2624_);
v_i_2587_ = v___x_2625_;
v_b_2588_ = v___x_2623_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_del_object(v___x_2605_);
lean_dec(v_snd_2603_);
v_a_2629_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2608_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2608_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_inh_2639_ = _args[0];
lean_object* v_as_2640_ = _args[1];
lean_object* v_sz_2641_ = _args[2];
lean_object* v_i_2642_ = _args[3];
lean_object* v_b_2643_ = _args[4];
lean_object* v___y_2644_ = _args[5];
lean_object* v___y_2645_ = _args[6];
lean_object* v___y_2646_ = _args[7];
lean_object* v___y_2647_ = _args[8];
lean_object* v___y_2648_ = _args[9];
lean_object* v___y_2649_ = _args[10];
lean_object* v___y_2650_ = _args[11];
lean_object* v___y_2651_ = _args[12];
lean_object* v___y_2652_ = _args[13];
lean_object* v___y_2653_ = _args[14];
lean_object* v___y_2654_ = _args[15];
lean_object* v___y_2655_ = _args[16];
_start:
{
size_t v_sz_boxed_2656_; size_t v_i_boxed_2657_; lean_object* v_res_2658_; 
v_sz_boxed_2656_ = lean_unbox_usize(v_sz_2641_);
lean_dec(v_sz_2641_);
v_i_boxed_2657_ = lean_unbox_usize(v_i_2642_);
lean_dec(v_i_2642_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_inh_2639_, v_as_2640_, v_sz_boxed_2656_, v_i_boxed_2657_, v_b_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v_as_2640_);
lean_dec(v_inh_2639_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_inh_2659_, lean_object* v_n_2660_, lean_object* v_b_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_inh_2659_, v_n_2660_, v_b_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec(v_inh_2659_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(lean_object* v_t_2675_, lean_object* v_init_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_root_2689_; lean_object* v_tail_2690_; lean_object* v___x_2691_; 
v_root_2689_ = lean_ctor_get(v_t_2675_, 0);
lean_inc_ref(v_root_2689_);
v_tail_2690_ = lean_ctor_get(v_t_2675_, 1);
lean_inc_ref(v_tail_2690_);
lean_dec_ref(v_t_2675_);
lean_inc(v_init_2676_);
v___x_2691_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_2676_, v_root_2689_, v_init_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v_init_2676_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2728_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2728_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2728_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
if (lean_obj_tag(v_a_2692_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; 
lean_dec_ref(v_tail_2690_);
v_a_2696_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v_a_2692_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v_a_2696_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; size_t v_sz_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
lean_del_object(v___x_2694_);
v_a_2700_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v_a_2692_);
v___x_2701_ = lean_box(0);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v_a_2700_);
v_sz_2703_ = lean_array_size(v_tail_2690_);
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_tail_2690_, v_sz_2703_, v___x_2704_, v___x_2702_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec_ref(v_tail_2690_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2719_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2719_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2719_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v_fst_2710_; 
v_fst_2710_ = lean_ctor_get(v_a_2706_, 0);
if (lean_obj_tag(v_fst_2710_) == 0)
{
lean_object* v_snd_2711_; lean_object* v___x_2713_; 
v_snd_2711_ = lean_ctor_get(v_a_2706_, 1);
lean_inc(v_snd_2711_);
lean_dec(v_a_2706_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v_snd_2711_);
v___x_2713_ = v___x_2708_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_snd_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
else
{
lean_object* v_val_2715_; lean_object* v___x_2717_; 
lean_inc_ref(v_fst_2710_);
lean_dec(v_a_2706_);
v_val_2715_ = lean_ctor_get(v_fst_2710_, 0);
lean_inc(v_val_2715_);
lean_dec_ref(v_fst_2710_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v_val_2715_);
v___x_2717_ = v___x_2708_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_val_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_a_2720_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2705_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2705_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v_tail_2690_);
v_a_2729_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2691_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2691_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_2737_, lean_object* v_init_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_t_2737_, v_init_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
return v_res_2751_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1));
v___x_2755_ = lean_unsigned_to_nat(2u);
v___x_2756_ = lean_unsigned_to_nat(73u);
v___x_2757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0));
v___x_2758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2759_ = l_mkPanicMessageWithDecl(v___x_2758_, v___x_2757_, v___x_2756_, v___x_2755_, v___x_2754_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v_vars_2774_; lean_object* v_diseqs_2775_; lean_object* v_size_2776_; lean_object* v_size_2777_; uint8_t v___x_2778_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref(v___x_2772_);
v_vars_2774_ = lean_ctor_get(v_a_2773_, 30);
lean_inc_ref(v_vars_2774_);
v_diseqs_2775_ = lean_ctor_get(v_a_2773_, 34);
lean_inc_ref(v_diseqs_2775_);
lean_dec(v_a_2773_);
v_size_2776_ = lean_ctor_get(v_vars_2774_, 2);
lean_inc(v_size_2776_);
lean_dec_ref(v_vars_2774_);
v_size_2777_ = lean_ctor_get(v_diseqs_2775_, 2);
v___x_2778_ = lean_nat_dec_eq(v_size_2776_, v_size_2777_);
lean_dec(v_size_2776_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec_ref(v_diseqs_2775_);
v___x_2779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2);
v___x_2780_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_2779_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_unsigned_to_nat(0u);
v___x_2782_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_diseqs_2775_, v___x_2781_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2790_; 
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v___x_2782_, 0);
lean_dec(v_unused_2791_);
v___x_2784_ = v___x_2782_;
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
else
{
lean_dec(v___x_2782_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2786_ = lean_box(0);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2786_);
v___x_2788_ = v___x_2784_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2782_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2782_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_a_2800_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2772_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2772_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___boxed(lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec(v_a_2808_);
return v_res_2820_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(lean_object* v_msg_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; lean_object* v___f_2836_; lean_object* v___x_5472__overap_2837_; lean_object* v___x_2838_; 
v___x_2835_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0);
v___f_2836_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2836_, 0, v___x_2835_);
v___x_5472__overap_2837_ = lean_panic_fn(v___f_2836_, v_msg_2822_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
lean_inc(v___y_2829_);
lean_inc_ref(v___y_2828_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc(v___y_2824_);
lean_inc(v___y_2823_);
v___x_2838_ = lean_apply_12(v___x_5472__overap_2837_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, lean_box(0));
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___boxed(lean_object* v_msg_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v_msg_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
return v_res_2852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3));
v___x_2855_ = lean_unsigned_to_nat(6u);
v___x_2856_ = lean_unsigned_to_nat(89u);
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_2858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2859_ = l_mkPanicMessageWithDecl(v___x_2858_, v___x_2857_, v___x_2856_, v___x_2855_, v___x_2854_);
return v___x_2859_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2));
v___x_2862_ = lean_unsigned_to_nat(6u);
v___x_2863_ = lean_unsigned_to_nat(87u);
v___x_2864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_2865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_2866_ = l_mkPanicMessageWithDecl(v___x_2865_, v___x_2864_, v___x_2863_, v___x_2862_, v___x_2861_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(lean_object* v_vars_2867_, lean_object* v_x_2868_, lean_object* v_____s_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_fst_2887_; lean_object* v_snd_2888_; lean_object* v_size_2889_; uint8_t v___x_2890_; 
v_fst_2887_ = lean_ctor_get(v_x_2868_, 0);
v_snd_2888_ = lean_ctor_get(v_x_2868_, 1);
v_size_2889_ = lean_ctor_get(v_vars_2867_, 2);
v___x_2890_ = lean_nat_dec_lt(v_snd_2888_, v_size_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec_ref(v_vars_2867_);
v___x_2891_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1);
v___x_2892_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_2891_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_dec_ref(v___x_2892_);
goto v___jp_2882_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2901_ = l_Lean_instInhabitedExpr;
v___x_2902_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2901_, v_vars_2867_, v_snd_2888_);
v___x_2903_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2887_, v___x_2902_);
lean_dec(v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3);
v___x_2905_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v___x_2904_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2905_;
}
else
{
goto v___jp_2882_;
}
}
v___jp_2882_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = lean_nat_add(v_____s_2869_, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed(lean_object* v_vars_2906_, lean_object* v_x_2907_, lean_object* v_____s_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(v_vars_2906_, v_x_2907_, v_____s_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec(v_____s_2908_);
lean_dec_ref(v_x_2907_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(lean_object* v_f_2922_, lean_object* v_s_2923_, lean_object* v_a_2924_, lean_object* v_b_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v_a_2924_);
lean_ctor_set(v___x_2938_, 1, v_b_2925_);
lean_inc(v___y_2936_);
lean_inc_ref(v___y_2935_);
lean_inc(v___y_2934_);
lean_inc_ref(v___y_2933_);
lean_inc(v___y_2932_);
lean_inc_ref(v___y_2931_);
lean_inc(v___y_2930_);
lean_inc_ref(v___y_2929_);
lean_inc(v___y_2928_);
lean_inc(v___y_2927_);
lean_inc(v___y_2926_);
v___x_2939_ = lean_apply_14(v_f_2922_, v___x_2938_, v_s_2923_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, lean_box(0));
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2966_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2966_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2966_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
if (lean_obj_tag(v_a_2940_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2954_; 
v_a_2944_ = lean_ctor_get(v_a_2940_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_a_2940_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2946_ = v_a_2940_;
v_isShared_2947_ = v_isSharedCheck_2954_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v_a_2940_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2954_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2951_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2949_);
v___x_2951_ = v___x_2942_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2965_; 
v_a_2955_ = lean_ctor_get(v_a_2940_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_a_2940_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2957_ = v_a_2940_;
v_isShared_2958_ = v_isSharedCheck_2965_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v_a_2940_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2965_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2962_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2960_);
v___x_2962_ = v___x_2942_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
v_a_2967_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2939_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2939_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed(lean_object* v_f_2975_, lean_object* v_s_2976_, lean_object* v_a_2977_, lean_object* v_b_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(v_f_2975_, v_s_2976_, v_a_2977_, v_b_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
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
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_2992_, lean_object* v_keys_2993_, lean_object* v_vals_2994_, lean_object* v_i_2995_, lean_object* v_acc_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = lean_array_get_size(v_keys_2993_);
v___x_3010_ = lean_nat_dec_lt(v_i_2995_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec(v_i_2995_);
lean_dec_ref(v_f_2992_);
v___x_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_acc_2996_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
else
{
lean_object* v_k_3013_; lean_object* v_v_3014_; lean_object* v___x_3015_; 
v_k_3013_ = lean_array_fget_borrowed(v_keys_2993_, v_i_2995_);
v_v_3014_ = lean_array_fget_borrowed(v_vals_2994_, v_i_2995_);
lean_inc_ref(v_f_2992_);
lean_inc(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc(v___y_2998_);
lean_inc(v___y_2997_);
lean_inc(v_v_3014_);
lean_inc(v_k_3013_);
v___x_3015_ = lean_apply_15(v_f_2992_, v_acc_2996_, v_k_3013_, v_v_3014_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, lean_box(0));
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
if (lean_obj_tag(v_a_3016_) == 0)
{
lean_dec_ref(v_a_3016_);
lean_dec(v_i_2995_);
lean_dec_ref(v_f_2992_);
return v___x_3015_;
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec_ref(v___x_3015_);
v_a_3017_ = lean_ctor_get(v_a_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref(v_a_3016_);
v___x_3018_ = lean_unsigned_to_nat(1u);
v___x_3019_ = lean_nat_add(v_i_2995_, v___x_3018_);
lean_dec(v_i_2995_);
v_i_2995_ = v___x_3019_;
v_acc_2996_ = v_a_3017_;
goto _start;
}
}
else
{
lean_dec(v_i_2995_);
lean_dec_ref(v_f_2992_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_f_3021_ = _args[0];
lean_object* v_keys_3022_ = _args[1];
lean_object* v_vals_3023_ = _args[2];
lean_object* v_i_3024_ = _args[3];
lean_object* v_acc_3025_ = _args[4];
lean_object* v___y_3026_ = _args[5];
lean_object* v___y_3027_ = _args[6];
lean_object* v___y_3028_ = _args[7];
lean_object* v___y_3029_ = _args[8];
lean_object* v___y_3030_ = _args[9];
lean_object* v___y_3031_ = _args[10];
lean_object* v___y_3032_ = _args[11];
lean_object* v___y_3033_ = _args[12];
lean_object* v___y_3034_ = _args[13];
lean_object* v___y_3035_ = _args[14];
lean_object* v___y_3036_ = _args[15];
lean_object* v___y_3037_ = _args[16];
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3021_, v_keys_3022_, v_vals_3023_, v_i_3024_, v_acc_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v_vals_3023_);
lean_dec_ref(v_keys_3022_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(lean_object* v_f_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
if (lean_obj_tag(v_x_3040_) == 0)
{
lean_object* v_es_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3076_; 
v_es_3054_ = lean_ctor_get(v_x_3040_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_x_3040_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3056_ = v_x_3040_;
v_isShared_3057_ = v_isSharedCheck_3076_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_es_3054_);
lean_dec(v_x_3040_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3076_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = lean_array_get_size(v_es_3054_);
v___x_3060_ = lean_nat_dec_lt(v___x_3058_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3062_; 
lean_dec_ref(v_es_3054_);
lean_dec_ref(v_f_3039_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 1);
lean_ctor_set(v___x_3056_, 0, v_x_3041_);
v___x_3062_ = v___x_3056_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_x_3041_);
v___x_3062_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
return v___x_3063_;
}
}
else
{
uint8_t v___x_3065_; 
v___x_3065_ = lean_nat_dec_le(v___x_3059_, v___x_3059_);
if (v___x_3065_ == 0)
{
if (v___x_3060_ == 0)
{
lean_object* v___x_3067_; 
lean_dec_ref(v_es_3054_);
lean_dec_ref(v_f_3039_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 1);
lean_ctor_set(v___x_3056_, 0, v_x_3041_);
v___x_3067_ = v___x_3056_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_x_3041_);
v___x_3067_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
else
{
size_t v___x_3070_; size_t v___x_3071_; lean_object* v___x_3072_; 
lean_del_object(v___x_3056_);
v___x_3070_ = ((size_t)0ULL);
v___x_3071_ = lean_usize_of_nat(v___x_3059_);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3039_, v_es_3054_, v___x_3070_, v___x_3071_, v_x_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec_ref(v_es_3054_);
return v___x_3072_;
}
}
else
{
size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
lean_del_object(v___x_3056_);
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = lean_usize_of_nat(v___x_3059_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3039_, v_es_3054_, v___x_3073_, v___x_3074_, v_x_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec_ref(v_es_3054_);
return v___x_3075_;
}
}
}
}
else
{
lean_object* v_ks_3077_; lean_object* v_vs_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_ks_3077_ = lean_ctor_get(v_x_3040_, 0);
lean_inc_ref(v_ks_3077_);
v_vs_3078_ = lean_ctor_get(v_x_3040_, 1);
lean_inc_ref(v_vs_3078_);
lean_dec_ref(v_x_3040_);
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3039_, v_ks_3077_, v_vs_3078_, v___x_3079_, v_x_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec_ref(v_vs_3078_);
lean_dec_ref(v_ks_3077_);
return v___x_3080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_3081_, lean_object* v_as_3082_, size_t v_i_3083_, size_t v_stop_3084_, lean_object* v_b_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_a_3099_; lean_object* v___y_3104_; uint8_t v___x_3107_; 
v___x_3107_ = lean_usize_dec_eq(v_i_3083_, v_stop_3084_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
v___x_3108_ = lean_array_uget_borrowed(v_as_3082_, v_i_3083_);
switch(lean_obj_tag(v___x_3108_))
{
case 0:
{
lean_object* v_key_3109_; lean_object* v_val_3110_; lean_object* v___x_3111_; 
v_key_3109_ = lean_ctor_get(v___x_3108_, 0);
v_val_3110_ = lean_ctor_get(v___x_3108_, 1);
lean_inc_ref(v_f_3081_);
lean_inc(v___y_3096_);
lean_inc_ref(v___y_3095_);
lean_inc(v___y_3094_);
lean_inc_ref(v___y_3093_);
lean_inc(v___y_3092_);
lean_inc_ref(v___y_3091_);
lean_inc(v___y_3090_);
lean_inc_ref(v___y_3089_);
lean_inc(v___y_3088_);
lean_inc(v___y_3087_);
lean_inc(v___y_3086_);
lean_inc(v_val_3110_);
lean_inc(v_key_3109_);
v___x_3111_ = lean_apply_15(v_f_3081_, v_b_3085_, v_key_3109_, v_val_3110_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, lean_box(0));
v___y_3104_ = v___x_3111_;
goto v___jp_3103_;
}
case 1:
{
lean_object* v_node_3112_; lean_object* v___x_3113_; 
v_node_3112_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_node_3112_);
lean_inc_ref(v_f_3081_);
v___x_3113_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3081_, v_node_3112_, v_b_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
v___y_3104_ = v___x_3113_;
goto v___jp_3103_;
}
default: 
{
v_a_3099_ = v_b_3085_;
goto v___jp_3098_;
}
}
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_dec_ref(v_f_3081_);
v___x_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3114_, 0, v_b_3085_);
v___x_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
return v___x_3115_;
}
v___jp_3098_:
{
size_t v___x_3100_; size_t v___x_3101_; 
v___x_3100_ = ((size_t)1ULL);
v___x_3101_ = lean_usize_add(v_i_3083_, v___x_3100_);
v_i_3083_ = v___x_3101_;
v_b_3085_ = v_a_3099_;
goto _start;
}
v___jp_3103_:
{
if (lean_obj_tag(v___y_3104_) == 0)
{
lean_object* v_a_3105_; 
v_a_3105_ = lean_ctor_get(v___y_3104_, 0);
if (lean_obj_tag(v_a_3105_) == 0)
{
lean_dec_ref(v_f_3081_);
return v___y_3104_;
}
else
{
lean_object* v_a_3106_; 
lean_inc_ref(v_a_3105_);
lean_dec_ref(v___y_3104_);
v_a_3106_ = lean_ctor_get(v_a_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v_a_3105_);
v_a_3099_ = v_a_3106_;
goto v___jp_3098_;
}
}
else
{
lean_dec_ref(v_f_3081_);
return v___y_3104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object** _args){
lean_object* v_f_3116_ = _args[0];
lean_object* v_as_3117_ = _args[1];
lean_object* v_i_3118_ = _args[2];
lean_object* v_stop_3119_ = _args[3];
lean_object* v_b_3120_ = _args[4];
lean_object* v___y_3121_ = _args[5];
lean_object* v___y_3122_ = _args[6];
lean_object* v___y_3123_ = _args[7];
lean_object* v___y_3124_ = _args[8];
lean_object* v___y_3125_ = _args[9];
lean_object* v___y_3126_ = _args[10];
lean_object* v___y_3127_ = _args[11];
lean_object* v___y_3128_ = _args[12];
lean_object* v___y_3129_ = _args[13];
lean_object* v___y_3130_ = _args[14];
lean_object* v___y_3131_ = _args[15];
lean_object* v___y_3132_ = _args[16];
_start:
{
size_t v_i_boxed_3133_; size_t v_stop_boxed_3134_; lean_object* v_res_3135_; 
v_i_boxed_3133_ = lean_unbox_usize(v_i_3118_);
lean_dec(v_i_3118_);
v_stop_boxed_3134_ = lean_unbox_usize(v_stop_3119_);
lean_dec(v_stop_3119_);
v_res_3135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3116_, v_as_3117_, v_i_boxed_3133_, v_stop_boxed_3134_, v_b_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v_as_3117_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_3136_, lean_object* v_x_3137_, lean_object* v_x_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3136_, v_x_3137_, v_x_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec(v___y_3139_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(lean_object* v_map_3152_, lean_object* v_init_3153_, lean_object* v_f_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___f_3167_; lean_object* v___x_3168_; 
v___f_3167_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed), 16, 1);
lean_closure_set(v___f_3167_, 0, v_f_3154_);
v___x_3168_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v___f_3167_, v_map_3152_, v_init_3153_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3177_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3177_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3177_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v_a_3173_; lean_object* v___x_3175_; 
v_a_3173_ = lean_ctor_get(v_a_3169_, 0);
lean_inc(v_a_3173_);
lean_dec(v_a_3169_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v_a_3173_);
v___x_3175_ = v___x_3171_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3173_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
v_a_3178_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3168_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3168_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___boxed(lean_object* v_map_3186_, lean_object* v_init_3187_, lean_object* v_f_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_3186_, v_init_3187_, v_f_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec(v___y_3189_);
return v_res_3201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0));
v___x_3204_ = lean_unsigned_to_nat(2u);
v___x_3205_ = lean_unsigned_to_nat(91u);
v___x_3206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0));
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_3208_ = l_mkPanicMessageWithDecl(v___x_3207_, v___x_3206_, v___x_3205_, v___x_3204_, v___x_3203_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v_vars_3223_; lean_object* v_varMap_3224_; lean_object* v___f_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref(v___x_3221_);
v_vars_3223_ = lean_ctor_get(v_a_3222_, 30);
lean_inc_ref(v_vars_3223_);
v_varMap_3224_ = lean_ctor_get(v_a_3222_, 31);
lean_inc_ref(v_varMap_3224_);
lean_dec(v_a_3222_);
lean_inc_ref(v_vars_3223_);
v___f_3225_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed), 15, 1);
lean_closure_set(v___f_3225_, 0, v_vars_3223_);
v___x_3226_ = lean_unsigned_to_nat(0u);
v___x_3227_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_varMap_3224_, v___x_3226_, v___f_3225_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3240_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3240_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3240_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v_size_3232_; uint8_t v___x_3233_; 
v_size_3232_ = lean_ctor_get(v_vars_3223_, 2);
lean_inc(v_size_3232_);
lean_dec_ref(v_vars_3223_);
v___x_3233_ = lean_nat_dec_eq(v_size_3232_, v_a_3228_);
lean_dec(v_a_3228_);
lean_dec(v_size_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_del_object(v___x_3230_);
v___x_3234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1);
v___x_3235_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3234_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
return v___x_3235_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = lean_box(0);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3236_);
v___x_3238_ = v___x_3230_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec_ref(v_vars_3223_);
v_a_3241_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3227_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3227_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
v_a_3249_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3221_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3221_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___boxed(lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
lean_dec(v_a_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec(v_a_3257_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(lean_object* v_00_u03c3_3270_, lean_object* v_00_u03b2_3271_, lean_object* v_map_3272_, lean_object* v_init_3273_, lean_object* v_f_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_3272_, v_init_3273_, v_f_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_3288_ = _args[0];
lean_object* v_00_u03b2_3289_ = _args[1];
lean_object* v_map_3290_ = _args[2];
lean_object* v_init_3291_ = _args[3];
lean_object* v_f_3292_ = _args[4];
lean_object* v___y_3293_ = _args[5];
lean_object* v___y_3294_ = _args[6];
lean_object* v___y_3295_ = _args[7];
lean_object* v___y_3296_ = _args[8];
lean_object* v___y_3297_ = _args[9];
lean_object* v___y_3298_ = _args[10];
lean_object* v___y_3299_ = _args[11];
lean_object* v___y_3300_ = _args[12];
lean_object* v___y_3301_ = _args[13];
lean_object* v___y_3302_ = _args[14];
lean_object* v___y_3303_ = _args[15];
lean_object* v___y_3304_ = _args[16];
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(v_00_u03c3_3288_, v_00_u03b2_3289_, v_map_3290_, v_init_3291_, v_f_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(lean_object* v_map_3306_, lean_object* v_f_3307_, lean_object* v_init_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3307_, v_map_3306_, v_init_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg___boxed(lean_object* v_map_3322_, lean_object* v_f_3323_, lean_object* v_init_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(v_map_3322_, v_f_3323_, v_init_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec(v___y_3325_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(lean_object* v_00_u03c3_3338_, lean_object* v_00_u03c3_3339_, lean_object* v_00_u03b2_3340_, lean_object* v_map_3341_, lean_object* v_f_3342_, lean_object* v_init_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3342_, v_map_3341_, v_init_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_3357_ = _args[0];
lean_object* v_00_u03c3_3358_ = _args[1];
lean_object* v_00_u03b2_3359_ = _args[2];
lean_object* v_map_3360_ = _args[3];
lean_object* v_f_3361_ = _args[4];
lean_object* v_init_3362_ = _args[5];
lean_object* v___y_3363_ = _args[6];
lean_object* v___y_3364_ = _args[7];
lean_object* v___y_3365_ = _args[8];
lean_object* v___y_3366_ = _args[9];
lean_object* v___y_3367_ = _args[10];
lean_object* v___y_3368_ = _args[11];
lean_object* v___y_3369_ = _args[12];
lean_object* v___y_3370_ = _args[13];
lean_object* v___y_3371_ = _args[14];
lean_object* v___y_3372_ = _args[15];
lean_object* v___y_3373_ = _args[16];
lean_object* v___y_3374_ = _args[17];
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(v_00_u03c3_3357_, v_00_u03c3_3358_, v_00_u03b2_3359_, v_map_3360_, v_f_3361_, v_init_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec(v___y_3363_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_3376_, lean_object* v_00_u03c3_3377_, lean_object* v_00_u03b1_3378_, lean_object* v_00_u03b2_3379_, lean_object* v_f_3380_, lean_object* v_x_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_3380_, v_x_3381_, v_x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_3396_ = _args[0];
lean_object* v_00_u03c3_3397_ = _args[1];
lean_object* v_00_u03b1_3398_ = _args[2];
lean_object* v_00_u03b2_3399_ = _args[3];
lean_object* v_f_3400_ = _args[4];
lean_object* v_x_3401_ = _args[5];
lean_object* v_x_3402_ = _args[6];
lean_object* v___y_3403_ = _args[7];
lean_object* v___y_3404_ = _args[8];
lean_object* v___y_3405_ = _args[9];
lean_object* v___y_3406_ = _args[10];
lean_object* v___y_3407_ = _args[11];
lean_object* v___y_3408_ = _args[12];
lean_object* v___y_3409_ = _args[13];
lean_object* v___y_3410_ = _args[14];
lean_object* v___y_3411_ = _args[15];
lean_object* v___y_3412_ = _args[16];
lean_object* v___y_3413_ = _args[17];
lean_object* v___y_3414_ = _args[18];
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(v_00_u03c3_3396_, v_00_u03c3_3397_, v_00_u03b1_3398_, v_00_u03b2_3399_, v_f_3400_, v_x_3401_, v_x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_3416_, lean_object* v_00_u03b2_3417_, lean_object* v_00_u03c3_3418_, lean_object* v_00_u03c3_3419_, lean_object* v_f_3420_, lean_object* v_as_3421_, size_t v_i_3422_, size_t v_stop_3423_, lean_object* v_b_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3420_, v_as_3421_, v_i_3422_, v_stop_3423_, v_b_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03b1_3438_ = _args[0];
lean_object* v_00_u03b2_3439_ = _args[1];
lean_object* v_00_u03c3_3440_ = _args[2];
lean_object* v_00_u03c3_3441_ = _args[3];
lean_object* v_f_3442_ = _args[4];
lean_object* v_as_3443_ = _args[5];
lean_object* v_i_3444_ = _args[6];
lean_object* v_stop_3445_ = _args[7];
lean_object* v_b_3446_ = _args[8];
lean_object* v___y_3447_ = _args[9];
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
_start:
{
size_t v_i_boxed_3459_; size_t v_stop_boxed_3460_; lean_object* v_res_3461_; 
v_i_boxed_3459_ = lean_unbox_usize(v_i_3444_);
lean_dec(v_i_3444_);
v_stop_boxed_3460_ = lean_unbox_usize(v_stop_3445_);
lean_dec(v_stop_3445_);
v_res_3461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_3438_, v_00_u03b2_3439_, v_00_u03c3_3440_, v_00_u03c3_3441_, v_f_3442_, v_as_3443_, v_i_boxed_3459_, v_stop_boxed_3460_, v_b_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v_as_3443_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_3462_, lean_object* v_00_u03c3_3463_, lean_object* v_00_u03b1_3464_, lean_object* v_00_u03b2_3465_, lean_object* v_f_3466_, lean_object* v_keys_3467_, lean_object* v_vals_3468_, lean_object* v_heq_3469_, lean_object* v_i_3470_, lean_object* v_acc_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3466_, v_keys_3467_, v_vals_3468_, v_i_3470_, v_acc_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03c3_3485_ = _args[0];
lean_object* v_00_u03c3_3486_ = _args[1];
lean_object* v_00_u03b1_3487_ = _args[2];
lean_object* v_00_u03b2_3488_ = _args[3];
lean_object* v_f_3489_ = _args[4];
lean_object* v_keys_3490_ = _args[5];
lean_object* v_vals_3491_ = _args[6];
lean_object* v_heq_3492_ = _args[7];
lean_object* v_i_3493_ = _args[8];
lean_object* v_acc_3494_ = _args[9];
lean_object* v___y_3495_ = _args[10];
lean_object* v___y_3496_ = _args[11];
lean_object* v___y_3497_ = _args[12];
lean_object* v___y_3498_ = _args[13];
lean_object* v___y_3499_ = _args[14];
lean_object* v___y_3500_ = _args[15];
lean_object* v___y_3501_ = _args[16];
lean_object* v___y_3502_ = _args[17];
lean_object* v___y_3503_ = _args[18];
lean_object* v___y_3504_ = _args[19];
lean_object* v___y_3505_ = _args[20];
lean_object* v___y_3506_ = _args[21];
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_3485_, v_00_u03c3_3486_, v_00_u03b1_3487_, v_00_u03b2_3488_, v_f_3489_, v_keys_3490_, v_vals_3491_, v_heq_3492_, v_i_3493_, v_acc_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v_vals_3491_);
lean_dec_ref(v_keys_3490_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v___x_3521_; 
lean_dec_ref(v___x_3520_);
v___x_3521_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3522_; 
lean_dec_ref(v___x_3521_);
v___x_3522_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3523_; 
lean_dec_ref(v___x_3522_);
v___x_3523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3523_;
}
else
{
return v___x_3522_;
}
}
else
{
return v___x_3521_;
}
}
else
{
return v___x_3520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs___boxed(lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec(v_a_3524_);
return v_res_3536_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1));
v___x_3540_ = lean_unsigned_to_nat(6u);
v___x_3541_ = lean_unsigned_to_nat(103u);
v___x_3542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0));
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0));
v___x_3544_ = l_mkPanicMessageWithDecl(v___x_3543_, v___x_3542_, v___x_3541_, v___x_3540_, v___x_3539_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(lean_object* v_upperBound_3545_, lean_object* v_a_3546_, lean_object* v_b_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
uint8_t v___x_3559_; 
v___x_3559_ = lean_nat_dec_lt(v_a_3546_, v_upperBound_3545_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; 
lean_dec(v_a_3546_);
v___x_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3560_, 0, v_b_3547_);
return v___x_3560_;
}
else
{
lean_object* v___x_3561_; lean_object* v___y_3563_; uint8_t v___x_3567_; 
v___x_3561_ = lean_box(0);
v___x_3567_ = lean_nat_dec_eq(v_a_3546_, v_a_3546_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2);
v___x_3569_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3568_, v_a_3546_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
v___y_3563_ = v___x_3569_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3570_; 
v___x_3570_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_3546_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
v___y_3563_ = v___x_3570_;
goto v___jp_3562_;
}
v___jp_3562_:
{
if (lean_obj_tag(v___y_3563_) == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec_ref(v___y_3563_);
v___x_3564_ = lean_unsigned_to_nat(1u);
v___x_3565_ = lean_nat_add(v_a_3546_, v___x_3564_);
lean_dec(v_a_3546_);
v_a_3546_ = v___x_3565_;
v_b_3547_ = v___x_3561_;
goto _start;
}
else
{
lean_dec(v_a_3546_);
return v___y_3563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___boxed(lean_object* v_upperBound_3571_, lean_object* v_a_3572_, lean_object* v_b_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_3571_, v_a_3572_, v_b_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec(v_upperBound_3571_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants(lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
uint8_t v_debug_3597_; 
v_debug_3597_ = lean_ctor_get_uint8(v_a_3588_, sizeof(void*)*7 + 2);
if (v_debug_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
return v___x_3599_;
}
else
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_3586_, v_a_3594_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v_structs_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref(v___x_3600_);
v_structs_3602_ = lean_ctor_get(v_a_3601_, 0);
lean_inc_ref(v_structs_3602_);
lean_dec(v_a_3601_);
v___x_3603_ = lean_array_get_size(v_structs_3602_);
lean_dec_ref(v_structs_3602_);
v___x_3604_ = lean_unsigned_to_nat(0u);
v___x_3605_ = lean_box(0);
v___x_3606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v___x_3603_, v___x_3604_, v___x_3605_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v___x_3606_, 0);
lean_dec(v_unused_3614_);
v___x_3608_ = v___x_3606_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_dec(v___x_3606_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3605_);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3605_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
return v___x_3606_;
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
v_a_3615_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3600_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3600_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed(lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_Meta_Grind_Arith_Linear_checkInvariants(v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec(v_a_3623_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(lean_object* v_upperBound_3635_, lean_object* v_inst_3636_, lean_object* v_R_3637_, lean_object* v_a_3638_, lean_object* v_b_3639_, lean_object* v_c_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_3635_, v_a_3638_, v_b_3639_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_3653_ = _args[0];
lean_object* v_inst_3654_ = _args[1];
lean_object* v_R_3655_ = _args[2];
lean_object* v_a_3656_ = _args[3];
lean_object* v_b_3657_ = _args[4];
lean_object* v_c_3658_ = _args[5];
lean_object* v___y_3659_ = _args[6];
lean_object* v___y_3660_ = _args[7];
lean_object* v___y_3661_ = _args[8];
lean_object* v___y_3662_ = _args[9];
lean_object* v___y_3663_ = _args[10];
lean_object* v___y_3664_ = _args[11];
lean_object* v___y_3665_ = _args[12];
lean_object* v___y_3666_ = _args[13];
lean_object* v___y_3667_ = _args[14];
lean_object* v___y_3668_ = _args[15];
lean_object* v___y_3669_ = _args[16];
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(v_upperBound_3653_, v_inst_3654_, v_R_3655_, v_a_3656_, v_b_3657_, v_c_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec(v_upperBound_3653_);
return v_res_3670_;
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
