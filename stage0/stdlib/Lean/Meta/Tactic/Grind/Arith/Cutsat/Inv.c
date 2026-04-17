// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
static lean_once_cell_t l_Int_Linear_Poly_checkCoeffs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_checkCoeffs___closed__0;
LEAN_EXPORT uint8_t l_Int_Linear_Poly_checkCoeffs(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkCoeffs___boxed(lean_object*);
static lean_once_cell_t l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_Linear_Poly_checkNoElimVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv"};
static const lean_object* l_Int_Linear_Poly_checkNoElimVars___closed__0 = (const lean_object*)&l_Int_Linear_Poly_checkNoElimVars___closed__0_value;
static const lean_string_object l_Int_Linear_Poly_checkNoElimVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Int.Linear.Poly.checkNoElimVars"};
static const lean_object* l_Int_Linear_Poly_checkNoElimVars___closed__1 = (const lean_object*)&l_Int_Linear_Poly_checkNoElimVars___closed__1_value;
static const lean_string_object l_Int_Linear_Poly_checkNoElimVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 111, .m_capacity = 111, .m_length = 110, .m_data = "assertion violation: !( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv.3550241989._hygCtx._hyg.34.0 )\n  "};
static const lean_object* l_Int_Linear_Poly_checkNoElimVars___closed__2 = (const lean_object*)&l_Int_Linear_Poly_checkNoElimVars___closed__2_value;
static lean_once_cell_t l_Int_Linear_Poly_checkNoElimVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_checkNoElimVars___closed__3;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkNoElimVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkNoElimVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv.0.Int.Linear.Poly.checkOccs.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 121, .m_capacity = 121, .m_length = 120, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv.24756299._hygCtx._hyg.67.0 ).contains y\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_Linear_Poly_checkCnstrOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Int.Linear.Poly.checkCnstrOf"};
static const lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__0 = (const lean_object*)&l_Int_Linear_Poly_checkCnstrOf___closed__0_value;
static const lean_string_object l_Int_Linear_Poly_checkCnstrOf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "assertion violation: x == y\n\n"};
static const lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__1 = (const lean_object*)&l_Int_Linear_Poly_checkCnstrOf___closed__1_value;
static lean_once_cell_t l_Int_Linear_Poly_checkCnstrOf___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__2;
static const lean_string_object l_Int_Linear_Poly_checkCnstrOf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__3 = (const lean_object*)&l_Int_Linear_Poly_checkCnstrOf___closed__3_value;
static lean_once_cell_t l_Int_Linear_Poly_checkCnstrOf___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__4;
static const lean_string_object l_Int_Linear_Poly_checkCnstrOf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: p.isSorted\n  "};
static const lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__5 = (const lean_object*)&l_Int_Linear_Poly_checkCnstrOf___closed__5_value;
static lean_once_cell_t l_Int_Linear_Poly_checkCnstrOf___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__6;
static const lean_string_object l_Int_Linear_Poly_checkCnstrOf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: p.checkCoeffs\n  "};
static const lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__7 = (const lean_object*)&l_Int_Linear_Poly_checkCnstrOf___closed__7_value;
static lean_once_cell_t l_Int_Linear_Poly_checkCnstrOf___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_checkCnstrOf___closed__8;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkCnstrOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkCnstrOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Meta.Grind.Arith.Cutsat.checkLeCnstrs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: isLower == (a < 0)\n    "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Grind.Arith.Cutsat.checkLowers"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: s.lowers.size == s.vars.size\n  "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Grind.Arith.Cutsat.checkUppers"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: s.uppers.size == s.vars.size\n  "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.Grind.Arith.Cutsat.checkDvds"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "assertion violation: c.d > 1\n    "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "assertion violation: s.vars.size == s.dvds.size\n  "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.Grind.Arith.Cutsat.checkVars"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "assertion violation: isSameExpr expr expr'\n    "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: s.vars.size == num\n\n"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___boxed(lean_object**);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Grind.Arith.Cutsat.checkElimEqs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "assertion violation: c.p.coeff x != 0\n    "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: c.p.isSorted\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: c.p.checkCoeffs\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "assertion violation: s.elimStack.contains x\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: s.elimEqs.size == s.vars.size\n  "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Meta.Grind.Arith.Cutsat.checkElimStack"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv.109525974._hygCtx._hyg.26.0 )\n\n"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Meta.Grind.Arith.Cutsat.checkDiseqCnstrs"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: s.vars.size == s.diseqs.size\n  "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Int_Linear_Poly_checkCoeffs___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_checkCoeffs(lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
else
{
lean_object* v_k_5_; lean_object* v_p_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_k_5_ = lean_ctor_get(v_x_3_, 0);
v_p_6_ = lean_ctor_get(v_x_3_, 2);
v___x_7_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_8_ = lean_int_dec_eq(v_k_5_, v___x_7_);
if (v___x_8_ == 0)
{
v_x_3_ = v_p_6_;
goto _start;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkCoeffs___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Int_Linear_Poly_checkCoeffs(v_x_11_);
lean_dec_ref(v_x_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
static lean_object* _init_l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(lean_object* v_msg_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_1598__overap_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_1598__overap_28_ = lean_panic_fn_borrowed(v___x_27_, v_msg_15_);
lean_inc(v___y_25_);
lean_inc_ref(v___y_24_);
lean_inc(v___y_23_);
lean_inc_ref(v___y_22_);
lean_inc(v___y_21_);
lean_inc_ref(v___y_20_);
lean_inc(v___y_19_);
lean_inc_ref(v___y_18_);
lean_inc(v___y_17_);
lean_inc(v___y_16_);
v___x_29_ = lean_apply_11(v___x_1598__overap_28_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, lean_box(0));
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___boxed(lean_object* v_msg_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v_msg_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec(v___y_31_);
return v_res_42_;
}
}
static lean_object* _init_l_Int_Linear_Poly_checkNoElimVars___closed__3(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__2));
v___x_47_ = lean_unsigned_to_nat(2u);
v___x_48_ = lean_unsigned_to_nat(23u);
v___x_49_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__1));
v___x_50_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_51_ = l_mkPanicMessageWithDecl(v___x_50_, v___x_49_, v___x_48_, v___x_47_, v___x_46_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkNoElimVars(lean_object* v_p_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
if (lean_obj_tag(v_p_52_) == 1)
{
lean_object* v_v_64_; lean_object* v_p_65_; lean_object* v___x_66_; 
v_v_64_ = lean_ctor_get(v_p_52_, 1);
v_p_65_ = lean_ctor_get(v_p_52_, 2);
v___x_66_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_v_64_, v_a_53_, v_a_61_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; uint8_t v___x_68_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref(v___x_66_);
v___x_68_ = lean_unbox(v_a_67_);
lean_dec(v_a_67_);
if (v___x_68_ == 0)
{
v_p_52_ = v_p_65_;
goto _start;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Int_Linear_Poly_checkNoElimVars___closed__3, &l_Int_Linear_Poly_checkNoElimVars___closed__3_once, _init_l_Int_Linear_Poly_checkNoElimVars___closed__3);
v___x_71_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_70_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
return v___x_71_;
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
v_a_72_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_66_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_66_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_box(0);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkNoElimVars___boxed(lean_object* v_p_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Int_Linear_Poly_checkNoElimVars(v_p_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec(v_a_83_);
lean_dec_ref(v_p_82_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(lean_object* v_k_95_, lean_object* v_t_96_){
_start:
{
if (lean_obj_tag(v_t_96_) == 0)
{
lean_object* v_k_97_; lean_object* v_l_98_; lean_object* v_r_99_; uint8_t v___x_100_; 
v_k_97_ = lean_ctor_get(v_t_96_, 1);
v_l_98_ = lean_ctor_get(v_t_96_, 3);
v_r_99_ = lean_ctor_get(v_t_96_, 4);
v___x_100_ = lean_nat_dec_lt(v_k_95_, v_k_97_);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; 
v___x_101_ = lean_nat_dec_eq(v_k_95_, v_k_97_);
if (v___x_101_ == 0)
{
v_t_96_ = v_r_99_;
goto _start;
}
else
{
return v___x_101_;
}
}
else
{
v_t_96_ = v_l_98_;
goto _start;
}
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg___boxed(lean_object* v_k_105_, lean_object* v_t_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_105_, v_t_106_);
lean_dec(v_t_106_);
lean_dec(v_k_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__1));
v___x_112_ = lean_unsigned_to_nat(4u);
v___x_113_ = lean_unsigned_to_nat(30u);
v___x_114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__0));
v___x_115_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_116_ = l_mkPanicMessageWithDecl(v___x_115_, v___x_114_, v___x_113_, v___x_112_, v___x_111_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go(lean_object* v_y_117_, lean_object* v_p_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
if (lean_obj_tag(v_p_118_) == 1)
{
lean_object* v_v_130_; lean_object* v_p_131_; lean_object* v___x_132_; 
v_v_130_ = lean_ctor_get(v_p_118_, 1);
v_p_131_ = lean_ctor_get(v_p_118_, 2);
v___x_132_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_v_130_, v_a_119_, v_a_127_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; uint8_t v___x_134_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref(v___x_132_);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(v_y_117_, v_a_133_);
lean_dec(v_a_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2);
v___x_136_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_135_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
return v___x_136_;
}
else
{
v_p_118_ = v_p_131_;
goto _start;
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_132_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_132_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___boxed(lean_object* v_y_148_, lean_object* v_p_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go(v_y_148_, v_p_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_p_149_);
lean_dec(v_y_148_);
return v_res_161_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0(lean_object* v_00_u03b2_162_, lean_object* v_k_163_, lean_object* v_t_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_163_, v_t_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___boxed(lean_object* v_00_u03b2_166_, lean_object* v_k_167_, lean_object* v_t_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0(v_00_u03b2_166_, v_k_167_, v_t_168_);
lean_dec(v_t_168_);
lean_dec(v_k_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkOccs(lean_object* v_p_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
if (lean_obj_tag(v_p_171_) == 1)
{
lean_object* v_v_183_; lean_object* v_p_184_; lean_object* v___x_185_; 
v_v_183_ = lean_ctor_get(v_p_171_, 1);
v_p_184_ = lean_ctor_get(v_p_171_, 2);
v___x_185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go(v_v_183_, v_p_184_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkOccs___boxed(lean_object* v_p_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Int_Linear_Poly_checkOccs(v_p_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_p_188_);
return v_res_200_;
}
}
static lean_object* _init_l_Int_Linear_Poly_checkCnstrOf___closed__2(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_203_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__1));
v___x_204_ = lean_unsigned_to_nat(2u);
v___x_205_ = lean_unsigned_to_nat(41u);
v___x_206_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__0));
v___x_207_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_208_ = l_mkPanicMessageWithDecl(v___x_207_, v___x_206_, v___x_205_, v___x_204_, v___x_203_);
return v___x_208_;
}
}
static lean_object* _init_l_Int_Linear_Poly_checkCnstrOf___closed__4(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__3));
v___x_211_ = lean_unsigned_to_nat(24u);
v___x_212_ = lean_unsigned_to_nat(40u);
v___x_213_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__0));
v___x_214_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_215_ = l_mkPanicMessageWithDecl(v___x_214_, v___x_213_, v___x_212_, v___x_211_, v___x_210_);
return v___x_215_;
}
}
static lean_object* _init_l_Int_Linear_Poly_checkCnstrOf___closed__6(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__5));
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_unsigned_to_nat(35u);
v___x_220_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__0));
v___x_221_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_222_ = l_mkPanicMessageWithDecl(v___x_221_, v___x_220_, v___x_219_, v___x_218_, v___x_217_);
return v___x_222_;
}
}
static lean_object* _init_l_Int_Linear_Poly_checkCnstrOf___closed__8(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__7));
v___x_225_ = lean_unsigned_to_nat(2u);
v___x_226_ = lean_unsigned_to_nat(36u);
v___x_227_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__0));
v___x_228_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_229_ = l_mkPanicMessageWithDecl(v___x_228_, v___x_227_, v___x_226_, v___x_225_, v___x_224_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkCnstrOf(lean_object* v_p_230_, lean_object* v_x_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; uint8_t v___x_262_; 
v___x_262_ = l_Int_Linear_Poly_isSorted(v_p_230_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l_Int_Linear_Poly_checkCnstrOf___closed__6, &l_Int_Linear_Poly_checkCnstrOf___closed__6_once, _init_l_Int_Linear_Poly_checkCnstrOf___closed__6);
v___x_264_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_263_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
return v___x_264_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = l_Int_Linear_Poly_checkCoeffs(v_p_230_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_obj_once(&l_Int_Linear_Poly_checkCnstrOf___closed__8, &l_Int_Linear_Poly_checkCnstrOf___closed__8_once, _init_l_Int_Linear_Poly_checkCnstrOf___closed__8);
v___x_267_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_266_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_232_, v_a_240_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; uint8_t v___x_270_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref(v___x_268_);
v___x_270_ = lean_unbox(v_a_269_);
lean_dec(v_a_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = l_Int_Linear_Poly_checkNoElimVars(v_p_230_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_272_; 
lean_dec_ref(v___x_271_);
v___x_272_ = l_Int_Linear_Poly_checkOccs(v_p_230_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_dec_ref(v___x_272_);
v___y_244_ = v_a_232_;
v___y_245_ = v_a_233_;
v___y_246_ = v_a_234_;
v___y_247_ = v_a_235_;
v___y_248_ = v_a_236_;
v___y_249_ = v_a_237_;
v___y_250_ = v_a_238_;
v___y_251_ = v_a_239_;
v___y_252_ = v_a_240_;
v___y_253_ = v_a_241_;
goto v___jp_243_;
}
else
{
return v___x_272_;
}
}
else
{
return v___x_271_;
}
}
else
{
v___y_244_ = v_a_232_;
v___y_245_ = v_a_233_;
v___y_246_ = v_a_234_;
v___y_247_ = v_a_235_;
v___y_248_ = v_a_236_;
v___y_249_ = v_a_237_;
v___y_250_ = v_a_238_;
v___y_251_ = v_a_239_;
v___y_252_ = v_a_240_;
v___y_253_ = v_a_241_;
goto v___jp_243_;
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_268_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_268_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
v___jp_243_:
{
if (lean_obj_tag(v_p_230_) == 1)
{
lean_object* v_v_254_; uint8_t v___x_255_; 
v_v_254_ = lean_ctor_get(v_p_230_, 1);
v___x_255_ = lean_nat_dec_eq(v_x_231_, v_v_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_obj_once(&l_Int_Linear_Poly_checkCnstrOf___closed__2, &l_Int_Linear_Poly_checkCnstrOf___closed__2_once, _init_l_Int_Linear_Poly_checkCnstrOf___closed__2);
v___x_257_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_256_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l_Int_Linear_Poly_checkCnstrOf___closed__4, &l_Int_Linear_Poly_checkCnstrOf___closed__4_once, _init_l_Int_Linear_Poly_checkCnstrOf___closed__4);
v___x_261_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_260_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_checkCnstrOf___boxed(lean_object* v_p_281_, lean_object* v_x_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Int_Linear_Poly_checkCnstrOf(v_p_281_, v_x_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec(v_a_283_);
lean_dec(v_x_282_);
lean_dec_ref(v_p_281_);
return v_res_294_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_3991__overap_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0);
v___x_3991__overap_309_ = lean_panic_fn_borrowed(v___x_308_, v_msg_296_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
lean_inc(v___y_298_);
lean_inc(v___y_297_);
v___x_310_ = lean_apply_11(v___x_3991__overap_309_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, lean_box(0));
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___boxed(lean_object* v_msg_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v_msg_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec(v___y_312_);
return v_res_323_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1));
v___x_327_ = lean_unsigned_to_nat(6u);
v___x_328_ = lean_unsigned_to_nat(49u);
v___x_329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_330_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_331_ = l_mkPanicMessageWithDecl(v___x_330_, v___x_329_, v___x_328_, v___x_327_, v___x_326_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_332_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__3));
v___x_333_ = lean_unsigned_to_nat(30u);
v___x_334_ = lean_unsigned_to_nat(48u);
v___x_335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_336_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_337_ = l_mkPanicMessageWithDecl(v___x_336_, v___x_335_, v___x_334_, v___x_333_, v___x_332_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object* v_____s_338_, uint8_t v_isLower_339_, lean_object* v_as_340_, size_t v_sz_341_, size_t v_i_342_, lean_object* v_b_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_usize_dec_lt(v_i_342_, v_sz_341_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v_b_343_);
return v___x_356_;
}
else
{
lean_object* v_snd_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_433_; 
v_snd_357_ = lean_ctor_get(v_b_343_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_b_343_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v_b_343_, 0);
lean_dec(v_unused_434_);
v___x_359_ = v_b_343_;
v_isShared_360_ = v_isSharedCheck_433_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snd_357_);
lean_dec(v_b_343_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_433_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_a_361_; lean_object* v_p_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_431_; 
v_a_361_ = lean_array_uget(v_as_340_, v_i_342_);
v_p_362_ = lean_ctor_get(v_a_361_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_a_361_, 1);
lean_dec(v_unused_432_);
v___x_364_ = v_a_361_;
v_isShared_365_ = v_isSharedCheck_431_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_p_362_);
lean_dec(v_a_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_431_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; 
v___x_366_ = l_Int_Linear_Poly_checkCnstrOf(v_p_362_, v_____s_338_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_367_; lean_object* v_a_369_; lean_object* v___x_407_; uint8_t v___y_409_; 
lean_dec_ref(v___x_366_);
v___x_367_ = lean_box(0);
v___x_407_ = lean_box(0);
if (lean_obj_tag(v_p_362_) == 1)
{
lean_object* v_k_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_k_410_ = lean_ctor_get(v_p_362_, 0);
lean_inc(v_k_410_);
lean_dec_ref(v_p_362_);
v___x_411_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_412_ = lean_int_dec_lt(v_k_410_, v___x_411_);
lean_dec(v_k_410_);
if (v_isLower_339_ == 0)
{
if (v___x_412_ == 0)
{
v___y_409_ = v___x_355_;
goto v___jp_408_;
}
else
{
goto v___jp_376_;
}
}
else
{
v___y_409_ = v___x_412_;
goto v___jp_408_;
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_del_object(v___x_364_);
lean_dec_ref(v_p_362_);
lean_dec(v_snd_357_);
v___x_413_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_414_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_413_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_dec_ref(v___x_414_);
v_a_369_ = v___x_407_;
goto v___jp_368_;
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_del_object(v___x_359_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
v___jp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_a_369_);
lean_ctor_set(v___x_359_, 0, v___x_367_);
v___x_371_ = v___x_359_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_a_369_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
size_t v___x_372_; size_t v___x_373_; 
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_add(v_i_342_, v___x_372_);
v_i_342_ = v___x_373_;
v_b_343_ = v___x_371_;
goto _start;
}
}
v___jp_376_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_378_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_377_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_398_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_398_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_398_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_398_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
if (lean_obj_tag(v_a_379_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_396_; 
lean_del_object(v___x_359_);
v_a_383_ = lean_ctor_get(v_a_379_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_a_379_);
if (v_isSharedCheck_396_ == 0)
{
v___x_385_ = v_a_379_;
v_isShared_386_ = v_isSharedCheck_396_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v_a_379_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_396_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 1);
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_395_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_snd_357_);
lean_ctor_set(v___x_364_, 0, v___x_388_);
v___x_390_ = v___x_364_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_snd_357_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_390_);
v___x_392_ = v___x_381_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v_a_397_; 
lean_del_object(v___x_381_);
lean_del_object(v___x_364_);
lean_dec(v_snd_357_);
v_a_397_ = lean_ctor_get(v_a_379_, 0);
lean_inc(v_a_397_);
lean_dec_ref(v_a_379_);
v_a_369_ = v_a_397_;
goto v___jp_368_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_del_object(v___x_364_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
v_a_399_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_378_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_378_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
v___jp_408_:
{
if (v___y_409_ == 0)
{
goto v___jp_376_;
}
else
{
lean_del_object(v___x_364_);
lean_dec(v_snd_357_);
v_a_369_ = v___x_407_;
goto v___jp_368_;
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_del_object(v___x_364_);
lean_dec_ref(v_p_362_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
v_a_423_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_366_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_366_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_____s_435_ = _args[0];
lean_object* v_isLower_436_ = _args[1];
lean_object* v_as_437_ = _args[2];
lean_object* v_sz_438_ = _args[3];
lean_object* v_i_439_ = _args[4];
lean_object* v_b_440_ = _args[5];
lean_object* v___y_441_ = _args[6];
lean_object* v___y_442_ = _args[7];
lean_object* v___y_443_ = _args[8];
lean_object* v___y_444_ = _args[9];
lean_object* v___y_445_ = _args[10];
lean_object* v___y_446_ = _args[11];
lean_object* v___y_447_ = _args[12];
lean_object* v___y_448_ = _args[13];
lean_object* v___y_449_ = _args[14];
lean_object* v___y_450_ = _args[15];
lean_object* v___y_451_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_452_; size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v_isLower_boxed_452_ = lean_unbox(v_isLower_436_);
v_sz_boxed_453_ = lean_unbox_usize(v_sz_438_);
lean_dec(v_sz_438_);
v_i_boxed_454_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_435_, v_isLower_boxed_452_, v_as_437_, v_sz_boxed_453_, v_i_boxed_454_, v_b_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v_as_437_);
lean_dec(v_____s_435_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(lean_object* v_____s_456_, uint8_t v_isLower_457_, lean_object* v_as_458_, size_t v_sz_459_, size_t v_i_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v_b_461_);
return v___x_474_;
}
else
{
lean_object* v_snd_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_551_; 
v_snd_475_ = lean_ctor_get(v_b_461_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_b_461_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_b_461_, 0);
lean_dec(v_unused_552_);
v___x_477_ = v_b_461_;
v_isShared_478_ = v_isSharedCheck_551_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_snd_475_);
lean_dec(v_b_461_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_551_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_a_479_; lean_object* v_p_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_549_; 
v_a_479_ = lean_array_uget(v_as_458_, v_i_460_);
v_p_480_ = lean_ctor_get(v_a_479_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v_a_479_, 1);
lean_dec(v_unused_550_);
v___x_482_ = v_a_479_;
v_isShared_483_ = v_isSharedCheck_549_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_p_480_);
lean_dec(v_a_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_549_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; 
v___x_484_ = l_Int_Linear_Poly_checkCnstrOf(v_p_480_, v_____s_456_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_a_488_; uint8_t v___y_527_; 
lean_dec_ref(v___x_484_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_box(0);
if (lean_obj_tag(v_p_480_) == 1)
{
lean_object* v_k_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_k_528_ = lean_ctor_get(v_p_480_, 0);
lean_inc(v_k_528_);
lean_dec_ref(v_p_480_);
v___x_529_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_530_ = lean_int_dec_lt(v_k_528_, v___x_529_);
lean_dec(v_k_528_);
if (v_isLower_457_ == 0)
{
if (v___x_530_ == 0)
{
v___y_527_ = v___x_473_;
goto v___jp_526_;
}
else
{
goto v___jp_495_;
}
}
else
{
v___y_527_ = v___x_530_;
goto v___jp_526_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_del_object(v___x_482_);
lean_dec_ref(v_p_480_);
lean_dec(v_snd_475_);
v___x_531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_532_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_531_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_dec_ref(v___x_532_);
v_a_488_ = v___x_485_;
goto v___jp_487_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_del_object(v___x_477_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
v___jp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v_a_488_);
lean_ctor_set(v___x_477_, 0, v___x_486_);
v___x_490_ = v___x_477_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_a_488_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_460_, v___x_491_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_456_, v_isLower_457_, v_as_458_, v_sz_459_, v___x_492_, v___x_490_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
return v___x_493_;
}
}
v___jp_495_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_497_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_496_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_517_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_517_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_517_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_517_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
if (lean_obj_tag(v_a_498_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_515_; 
lean_del_object(v___x_477_);
v_a_502_ = lean_ctor_get(v_a_498_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_a_498_);
if (v_isSharedCheck_515_ == 0)
{
v___x_504_ = v_a_498_;
v_isShared_505_ = v_isSharedCheck_515_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v_a_498_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_515_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 1);
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_514_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v_snd_475_);
lean_ctor_set(v___x_482_, 0, v___x_507_);
v___x_509_ = v___x_482_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_snd_475_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_509_);
v___x_511_ = v___x_500_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
else
{
lean_object* v_a_516_; 
lean_del_object(v___x_500_);
lean_del_object(v___x_482_);
lean_dec(v_snd_475_);
v_a_516_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v_a_498_);
v_a_488_ = v_a_516_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_del_object(v___x_482_);
lean_del_object(v___x_477_);
lean_dec(v_snd_475_);
v_a_518_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_497_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_497_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
goto v___jp_495_;
}
else
{
lean_del_object(v___x_482_);
lean_dec(v_snd_475_);
v_a_488_ = v___x_485_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_del_object(v___x_482_);
lean_dec_ref(v_p_480_);
lean_del_object(v___x_477_);
lean_dec(v_snd_475_);
v_a_541_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_484_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_484_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_553_ = _args[0];
lean_object* v_isLower_554_ = _args[1];
lean_object* v_as_555_ = _args[2];
lean_object* v_sz_556_ = _args[3];
lean_object* v_i_557_ = _args[4];
lean_object* v_b_558_ = _args[5];
lean_object* v___y_559_ = _args[6];
lean_object* v___y_560_ = _args[7];
lean_object* v___y_561_ = _args[8];
lean_object* v___y_562_ = _args[9];
lean_object* v___y_563_ = _args[10];
lean_object* v___y_564_ = _args[11];
lean_object* v___y_565_ = _args[12];
lean_object* v___y_566_ = _args[13];
lean_object* v___y_567_ = _args[14];
lean_object* v___y_568_ = _args[15];
lean_object* v___y_569_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_570_; size_t v_sz_boxed_571_; size_t v_i_boxed_572_; lean_object* v_res_573_; 
v_isLower_boxed_570_ = lean_unbox(v_isLower_554_);
v_sz_boxed_571_ = lean_unbox_usize(v_sz_556_);
lean_dec(v_sz_556_);
v_i_boxed_572_ = lean_unbox_usize(v_i_557_);
lean_dec(v_i_557_);
v_res_573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_553_, v_isLower_boxed_570_, v_as_555_, v_sz_boxed_571_, v_i_boxed_572_, v_b_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v_as_555_);
lean_dec(v_____s_553_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object* v_____s_574_, uint8_t v_isLower_575_, lean_object* v_as_576_, size_t v_sz_577_, size_t v_i_578_, lean_object* v_b_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_lt(v_i_578_, v_sz_577_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_b_579_);
return v___x_592_;
}
else
{
lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_662_; 
v_snd_593_ = lean_ctor_get(v_b_579_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_b_579_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_b_579_, 0);
lean_dec(v_unused_663_);
v___x_595_ = v_b_579_;
v_isShared_596_ = v_isSharedCheck_662_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_dec(v_b_579_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_662_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_a_597_; lean_object* v_p_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_660_; 
v_a_597_ = lean_array_uget(v_as_576_, v_i_578_);
v_p_598_ = lean_ctor_get(v_a_597_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_597_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v_a_597_, 1);
lean_dec(v_unused_661_);
v___x_600_ = v_a_597_;
v_isShared_601_ = v_isSharedCheck_660_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_p_598_);
lean_dec(v_a_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_660_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; 
v___x_602_ = l_Int_Linear_Poly_checkCnstrOf(v_p_598_, v_____s_574_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_603_; lean_object* v_a_605_; lean_object* v___x_636_; uint8_t v___y_638_; 
lean_dec_ref(v___x_602_);
v___x_603_ = lean_box(0);
v___x_636_ = lean_box(0);
if (lean_obj_tag(v_p_598_) == 1)
{
lean_object* v_k_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_k_639_ = lean_ctor_get(v_p_598_, 0);
lean_inc(v_k_639_);
lean_dec_ref(v_p_598_);
v___x_640_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_641_ = lean_int_dec_lt(v_k_639_, v___x_640_);
lean_dec(v_k_639_);
if (v_isLower_575_ == 0)
{
if (v___x_641_ == 0)
{
v___y_638_ = v___x_591_;
goto v___jp_637_;
}
else
{
goto v___jp_612_;
}
}
else
{
v___y_638_ = v___x_641_;
goto v___jp_637_;
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_del_object(v___x_600_);
lean_dec_ref(v_p_598_);
lean_dec(v_snd_593_);
v___x_642_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_643_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_642_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref(v___x_643_);
v_a_605_ = v___x_636_;
goto v___jp_604_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_del_object(v___x_595_);
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
v___jp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v_a_605_);
lean_ctor_set(v___x_595_, 0, v___x_603_);
v___x_607_ = v___x_595_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_a_605_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
size_t v___x_608_; size_t v___x_609_; 
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_578_, v___x_608_);
v_i_578_ = v___x_609_;
v_b_579_ = v___x_607_;
goto _start;
}
}
v___jp_612_:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_614_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_613_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_627_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_627_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
if (lean_obj_tag(v_a_615_) == 0)
{
lean_object* v___x_619_; lean_object* v___x_621_; 
lean_del_object(v___x_595_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v_a_615_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v_snd_593_);
lean_ctor_set(v___x_600_, 0, v___x_619_);
v___x_621_ = v___x_600_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_snd_593_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
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
}
else
{
lean_object* v_a_626_; 
lean_del_object(v___x_617_);
lean_del_object(v___x_600_);
lean_dec(v_snd_593_);
v_a_626_ = lean_ctor_get(v_a_615_, 0);
lean_inc(v_a_626_);
lean_dec_ref(v_a_615_);
v_a_605_ = v_a_626_;
goto v___jp_604_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_del_object(v___x_600_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_628_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_614_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_614_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
v___jp_637_:
{
if (v___y_638_ == 0)
{
goto v___jp_612_;
}
else
{
lean_del_object(v___x_600_);
lean_dec(v_snd_593_);
v_a_605_ = v___x_636_;
goto v___jp_604_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_del_object(v___x_600_);
lean_dec_ref(v_p_598_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_652_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_602_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_602_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_____s_664_ = _args[0];
lean_object* v_isLower_665_ = _args[1];
lean_object* v_as_666_ = _args[2];
lean_object* v_sz_667_ = _args[3];
lean_object* v_i_668_ = _args[4];
lean_object* v_b_669_ = _args[5];
lean_object* v___y_670_ = _args[6];
lean_object* v___y_671_ = _args[7];
lean_object* v___y_672_ = _args[8];
lean_object* v___y_673_ = _args[9];
lean_object* v___y_674_ = _args[10];
lean_object* v___y_675_ = _args[11];
lean_object* v___y_676_ = _args[12];
lean_object* v___y_677_ = _args[13];
lean_object* v___y_678_ = _args[14];
lean_object* v___y_679_ = _args[15];
lean_object* v___y_680_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_681_; size_t v_sz_boxed_682_; size_t v_i_boxed_683_; lean_object* v_res_684_; 
v_isLower_boxed_681_ = lean_unbox(v_isLower_665_);
v_sz_boxed_682_ = lean_unbox_usize(v_sz_667_);
lean_dec(v_sz_667_);
v_i_boxed_683_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_res_684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_664_, v_isLower_boxed_681_, v_as_666_, v_sz_boxed_682_, v_i_boxed_683_, v_b_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v_as_666_);
lean_dec(v_____s_664_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object* v_____s_685_, uint8_t v_isLower_686_, lean_object* v_as_687_, size_t v_sz_688_, size_t v_i_689_, lean_object* v_b_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v_b_690_);
return v___x_703_;
}
else
{
lean_object* v_snd_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_773_; 
v_snd_704_ = lean_ctor_get(v_b_690_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_b_690_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_b_690_, 0);
lean_dec(v_unused_774_);
v___x_706_ = v_b_690_;
v_isShared_707_ = v_isSharedCheck_773_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_snd_704_);
lean_dec(v_b_690_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_773_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_a_708_; lean_object* v_p_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_771_; 
v_a_708_ = lean_array_uget(v_as_687_, v_i_689_);
v_p_709_ = lean_ctor_get(v_a_708_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_a_708_, 1);
lean_dec(v_unused_772_);
v___x_711_ = v_a_708_;
v_isShared_712_ = v_isSharedCheck_771_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_p_709_);
lean_dec(v_a_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_771_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; 
v___x_713_ = l_Int_Linear_Poly_checkCnstrOf(v_p_709_, v_____s_685_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_a_717_; uint8_t v___y_749_; 
lean_dec_ref(v___x_713_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_box(0);
if (lean_obj_tag(v_p_709_) == 1)
{
lean_object* v_k_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_k_750_ = lean_ctor_get(v_p_709_, 0);
lean_inc(v_k_750_);
lean_dec_ref(v_p_709_);
v___x_751_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_752_ = lean_int_dec_lt(v_k_750_, v___x_751_);
lean_dec(v_k_750_);
if (v_isLower_686_ == 0)
{
if (v___x_752_ == 0)
{
v___y_749_ = v___x_702_;
goto v___jp_748_;
}
else
{
goto v___jp_724_;
}
}
else
{
v___y_749_ = v___x_752_;
goto v___jp_748_;
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_del_object(v___x_711_);
lean_dec_ref(v_p_709_);
lean_dec(v_snd_704_);
v___x_753_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_754_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_753_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_dec_ref(v___x_754_);
v_a_717_ = v___x_714_;
goto v___jp_716_;
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_del_object(v___x_706_);
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
v___jp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v_a_717_);
lean_ctor_set(v___x_706_, 0, v___x_715_);
v___x_719_ = v___x_706_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_a_717_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
size_t v___x_720_; size_t v___x_721_; lean_object* v___x_722_; 
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_i_689_, v___x_720_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_685_, v_isLower_686_, v_as_687_, v_sz_688_, v___x_721_, v___x_719_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
return v___x_722_;
}
}
v___jp_724_:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_726_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_725_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_739_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_739_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_739_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_739_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
if (lean_obj_tag(v_a_727_) == 0)
{
lean_object* v___x_731_; lean_object* v___x_733_; 
lean_del_object(v___x_706_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_a_727_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v_snd_704_);
lean_ctor_set(v___x_711_, 0, v___x_731_);
v___x_733_ = v___x_711_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_snd_704_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_733_);
v___x_735_ = v___x_729_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v_a_738_; 
lean_del_object(v___x_729_);
lean_del_object(v___x_711_);
lean_dec(v_snd_704_);
v_a_738_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_a_738_);
lean_dec_ref(v_a_727_);
v_a_717_ = v_a_738_;
goto v___jp_716_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_del_object(v___x_711_);
lean_del_object(v___x_706_);
lean_dec(v_snd_704_);
v_a_740_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_726_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_726_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
v___jp_748_:
{
if (v___y_749_ == 0)
{
goto v___jp_724_;
}
else
{
lean_del_object(v___x_711_);
lean_dec(v_snd_704_);
v_a_717_ = v___x_714_;
goto v___jp_716_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_del_object(v___x_711_);
lean_dec_ref(v_p_709_);
lean_del_object(v___x_706_);
lean_dec(v_snd_704_);
v_a_763_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_713_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_713_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_____s_775_ = _args[0];
lean_object* v_isLower_776_ = _args[1];
lean_object* v_as_777_ = _args[2];
lean_object* v_sz_778_ = _args[3];
lean_object* v_i_779_ = _args[4];
lean_object* v_b_780_ = _args[5];
lean_object* v___y_781_ = _args[6];
lean_object* v___y_782_ = _args[7];
lean_object* v___y_783_ = _args[8];
lean_object* v___y_784_ = _args[9];
lean_object* v___y_785_ = _args[10];
lean_object* v___y_786_ = _args[11];
lean_object* v___y_787_ = _args[12];
lean_object* v___y_788_ = _args[13];
lean_object* v___y_789_ = _args[14];
lean_object* v___y_790_ = _args[15];
lean_object* v___y_791_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_792_; size_t v_sz_boxed_793_; size_t v_i_boxed_794_; lean_object* v_res_795_; 
v_isLower_boxed_792_ = lean_unbox(v_isLower_776_);
v_sz_boxed_793_ = lean_unbox_usize(v_sz_778_);
lean_dec(v_sz_778_);
v_i_boxed_794_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_res_795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_775_, v_isLower_boxed_792_, v_as_777_, v_sz_boxed_793_, v_i_boxed_794_, v_b_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v_as_777_);
lean_dec(v_____s_775_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(lean_object* v_init_796_, lean_object* v_____s_797_, uint8_t v_isLower_798_, lean_object* v_n_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
if (lean_obj_tag(v_n_799_) == 0)
{
lean_object* v_cs_812_; lean_object* v___x_813_; lean_object* v___x_814_; size_t v_sz_815_; size_t v___x_816_; lean_object* v___x_817_; 
v_cs_812_ = lean_ctor_get(v_n_799_, 0);
v___x_813_ = lean_box(0);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_b_800_);
v_sz_815_ = lean_array_size(v_cs_812_);
v___x_816_ = ((size_t)0ULL);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_796_, v_____s_797_, v_isLower_798_, v_cs_812_, v_sz_815_, v___x_816_, v___x_814_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_832_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_832_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_fst_822_; 
v_fst_822_ = lean_ctor_get(v_a_818_, 0);
if (lean_obj_tag(v_fst_822_) == 0)
{
lean_object* v_snd_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v_snd_823_ = lean_ctor_get(v_a_818_, 1);
lean_inc(v_snd_823_);
lean_dec(v_a_818_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_snd_823_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_824_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
lean_object* v_val_828_; lean_object* v___x_830_; 
lean_inc_ref(v_fst_822_);
lean_dec(v_a_818_);
v_val_828_ = lean_ctor_get(v_fst_822_, 0);
lean_inc(v_val_828_);
lean_dec_ref(v_fst_822_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_val_828_);
v___x_830_ = v___x_820_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_val_828_);
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
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_a_833_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_817_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_817_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_vs_841_; lean_object* v___x_842_; lean_object* v___x_843_; size_t v_sz_844_; size_t v___x_845_; lean_object* v___x_846_; 
v_vs_841_ = lean_ctor_get(v_n_799_, 0);
v___x_842_ = lean_box(0);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v_b_800_);
v_sz_844_ = lean_array_size(v_vs_841_);
v___x_845_ = ((size_t)0ULL);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_797_, v_isLower_798_, v_vs_841_, v_sz_844_, v___x_845_, v___x_843_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_861_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_861_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_861_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_861_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_fst_851_; 
v_fst_851_ = lean_ctor_get(v_a_847_, 0);
if (lean_obj_tag(v_fst_851_) == 0)
{
lean_object* v_snd_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v_snd_852_ = lean_ctor_get(v_a_847_, 1);
lean_inc(v_snd_852_);
lean_dec(v_a_847_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v_snd_852_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_853_);
v___x_855_ = v___x_849_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
lean_object* v_val_857_; lean_object* v___x_859_; 
lean_inc_ref(v_fst_851_);
lean_dec(v_a_847_);
v_val_857_ = lean_ctor_get(v_fst_851_, 0);
lean_inc(v_val_857_);
lean_dec_ref(v_fst_851_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v_val_857_);
v___x_859_ = v___x_849_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_val_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_846_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_846_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_init_870_, lean_object* v_____s_871_, uint8_t v_isLower_872_, lean_object* v_as_873_, size_t v_sz_874_, size_t v_i_875_, lean_object* v_b_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_lt(v_i_875_, v_sz_874_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v_b_876_);
return v___x_889_;
}
else
{
lean_object* v_snd_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_924_; 
v_snd_890_ = lean_ctor_get(v_b_876_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_b_876_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v_b_876_, 0);
lean_dec(v_unused_925_);
v___x_892_ = v_b_876_;
v_isShared_893_ = v_isSharedCheck_924_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_snd_890_);
lean_dec(v_b_876_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_924_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_a_894_; lean_object* v___x_895_; 
v_a_894_ = lean_array_uget_borrowed(v_as_873_, v_i_875_);
lean_inc(v_snd_890_);
v___x_895_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_870_, v_____s_871_, v_isLower_872_, v_a_894_, v_snd_890_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_915_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_915_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_915_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_915_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
if (lean_obj_tag(v_a_896_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v_a_896_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_900_);
v___x_902_ = v___x_892_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_snd_890_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_902_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
lean_del_object(v___x_898_);
lean_dec(v_snd_890_);
v_a_907_ = lean_ctor_get(v_a_896_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v_a_896_);
v___x_908_ = lean_box(0);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v_a_907_);
lean_ctor_set(v___x_892_, 0, v___x_908_);
v___x_910_ = v___x_892_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_a_907_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
size_t v___x_911_; size_t v___x_912_; 
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_875_, v___x_911_);
v_i_875_ = v___x_912_;
v_b_876_ = v___x_910_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_del_object(v___x_892_);
lean_dec(v_snd_890_);
v_a_916_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_895_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_895_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_926_ = _args[0];
lean_object* v_____s_927_ = _args[1];
lean_object* v_isLower_928_ = _args[2];
lean_object* v_as_929_ = _args[3];
lean_object* v_sz_930_ = _args[4];
lean_object* v_i_931_ = _args[5];
lean_object* v_b_932_ = _args[6];
lean_object* v___y_933_ = _args[7];
lean_object* v___y_934_ = _args[8];
lean_object* v___y_935_ = _args[9];
lean_object* v___y_936_ = _args[10];
lean_object* v___y_937_ = _args[11];
lean_object* v___y_938_ = _args[12];
lean_object* v___y_939_ = _args[13];
lean_object* v___y_940_ = _args[14];
lean_object* v___y_941_ = _args[15];
lean_object* v___y_942_ = _args[16];
lean_object* v___y_943_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_944_; size_t v_sz_boxed_945_; size_t v_i_boxed_946_; lean_object* v_res_947_; 
v_isLower_boxed_944_ = lean_unbox(v_isLower_928_);
v_sz_boxed_945_ = lean_unbox_usize(v_sz_930_);
lean_dec(v_sz_930_);
v_i_boxed_946_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_926_, v_____s_927_, v_isLower_boxed_944_, v_as_929_, v_sz_boxed_945_, v_i_boxed_946_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v_as_929_);
lean_dec(v_____s_927_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1___boxed(lean_object* v_init_948_, lean_object* v_____s_949_, lean_object* v_isLower_950_, lean_object* v_n_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
uint8_t v_isLower_boxed_964_; lean_object* v_res_965_; 
v_isLower_boxed_964_ = lean_unbox(v_isLower_950_);
v_res_965_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_948_, v_____s_949_, v_isLower_boxed_964_, v_n_951_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v_n_951_);
lean_dec(v_____s_949_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(lean_object* v_____s_966_, uint8_t v_isLower_967_, lean_object* v_t_968_, lean_object* v_init_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_root_981_; lean_object* v_tail_982_; lean_object* v___x_983_; 
v_root_981_ = lean_ctor_get(v_t_968_, 0);
v_tail_982_ = lean_ctor_get(v_t_968_, 1);
v___x_983_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_969_, v_____s_966_, v_isLower_967_, v_root_981_, v_init_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1020_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_1020_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1020_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
if (lean_obj_tag(v_a_984_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v_a_984_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v_a_988_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; size_t v_sz_995_; size_t v___x_996_; lean_object* v___x_997_; 
lean_del_object(v___x_986_);
v_a_992_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v_a_984_);
v___x_993_ = lean_box(0);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v_a_992_);
v_sz_995_ = lean_array_size(v_tail_982_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_966_, v_isLower_967_, v_tail_982_, v_sz_995_, v___x_996_, v___x_994_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1011_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_fst_1002_; 
v_fst_1002_ = lean_ctor_get(v_a_998_, 0);
if (lean_obj_tag(v_fst_1002_) == 0)
{
lean_object* v_snd_1003_; lean_object* v___x_1005_; 
v_snd_1003_ = lean_ctor_get(v_a_998_, 1);
lean_inc(v_snd_1003_);
lean_dec(v_a_998_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_snd_1003_);
v___x_1005_ = v___x_1000_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_snd_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1009_; 
lean_inc_ref(v_fst_1002_);
lean_dec(v_a_998_);
v_val_1007_ = lean_ctor_get(v_fst_1002_, 0);
lean_inc(v_val_1007_);
lean_dec_ref(v_fst_1002_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_val_1007_);
v___x_1009_ = v___x_1000_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_val_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_997_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_997_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_983_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_983_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1029_, lean_object* v_isLower_1030_, lean_object* v_t_1031_, lean_object* v_init_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
uint8_t v_isLower_boxed_1044_; lean_object* v_res_1045_; 
v_isLower_boxed_1044_ = lean_unbox(v_isLower_1030_);
v_res_1045_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_____s_1029_, v_isLower_boxed_1044_, v_t_1031_, v_init_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v_t_1031_);
lean_dec(v_____s_1029_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1046_, lean_object* v_as_1047_, size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_b_1050_);
return v___x_1063_;
}
else
{
lean_object* v_snd_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1088_; 
v_snd_1064_ = lean_ctor_get(v_b_1050_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_b_1050_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_b_1050_, 0);
lean_dec(v_unused_1089_);
v___x_1066_ = v_b_1050_;
v_isShared_1067_ = v_isSharedCheck_1088_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snd_1064_);
lean_dec(v_b_1050_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1088_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_a_1068_ = lean_array_uget_borrowed(v_as_1047_, v_i_1049_);
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1064_, v_isLower_1046_, v_a_1068_, v___x_1069_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_dec_ref(v___x_1070_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_nat_add(v_snd_1064_, v___x_1072_);
lean_dec(v_snd_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1073_);
lean_ctor_set(v___x_1066_, 0, v___x_1071_);
v___x_1075_ = v___x_1066_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
size_t v___x_1076_; size_t v___x_1077_; 
v___x_1076_ = ((size_t)1ULL);
v___x_1077_ = lean_usize_add(v_i_1049_, v___x_1076_);
v_i_1049_ = v___x_1077_;
v_b_1050_ = v___x_1075_;
goto _start;
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_del_object(v___x_1066_);
lean_dec(v_snd_1064_);
v_a_1080_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1070_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1070_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object* v_isLower_1090_, lean_object* v_as_1091_, lean_object* v_sz_1092_, lean_object* v_i_1093_, lean_object* v_b_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_isLower_boxed_1106_; size_t v_sz_boxed_1107_; size_t v_i_boxed_1108_; lean_object* v_res_1109_; 
v_isLower_boxed_1106_ = lean_unbox(v_isLower_1090_);
v_sz_boxed_1107_ = lean_unbox_usize(v_sz_1092_);
lean_dec(v_sz_1092_);
v_i_boxed_1108_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_res_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_1106_, v_as_1091_, v_sz_boxed_1107_, v_i_boxed_1108_, v_b_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v_as_1091_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1110_, lean_object* v_as_1111_, size_t v_sz_1112_, size_t v_i_1113_, lean_object* v_b_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_usize_dec_lt(v_i_1113_, v_sz_1112_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_b_1114_);
return v___x_1127_;
}
else
{
lean_object* v_snd_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1152_; 
v_snd_1128_ = lean_ctor_get(v_b_1114_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_b_1114_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v_b_1114_, 0);
lean_dec(v_unused_1153_);
v___x_1130_ = v_b_1114_;
v_isShared_1131_ = v_isSharedCheck_1152_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snd_1128_);
lean_dec(v_b_1114_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1152_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_a_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_a_1132_ = lean_array_uget_borrowed(v_as_1111_, v_i_1113_);
v___x_1133_ = lean_box(0);
v___x_1134_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1128_, v_isLower_1110_, v_a_1132_, v___x_1133_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec_ref(v___x_1134_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_add(v_snd_1128_, v___x_1136_);
lean_dec(v_snd_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v___x_1137_);
lean_ctor_set(v___x_1130_, 0, v___x_1135_);
v___x_1139_ = v___x_1130_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_add(v_i_1113_, v___x_1140_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1110_, v_as_1111_, v_sz_1112_, v___x_1141_, v___x_1139_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1142_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_del_object(v___x_1130_);
lean_dec(v_snd_1128_);
v_a_1144_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1134_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1134_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5___boxed(lean_object* v_isLower_1154_, lean_object* v_as_1155_, lean_object* v_sz_1156_, lean_object* v_i_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v_isLower_boxed_1170_; size_t v_sz_boxed_1171_; size_t v_i_boxed_1172_; lean_object* v_res_1173_; 
v_isLower_boxed_1170_ = lean_unbox(v_isLower_1154_);
v_sz_boxed_1171_ = lean_unbox_usize(v_sz_1156_);
lean_dec(v_sz_1156_);
v_i_boxed_1172_ = lean_unbox_usize(v_i_1157_);
lean_dec(v_i_1157_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1170_, v_as_1155_, v_sz_boxed_1171_, v_i_boxed_1172_, v_b_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v_as_1155_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1174_, lean_object* v_as_1175_, size_t v_sz_1176_, size_t v_i_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_usize_dec_lt(v_i_1177_, v_sz_1176_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_b_1178_);
return v___x_1191_;
}
else
{
lean_object* v_snd_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1216_; 
v_snd_1192_ = lean_ctor_get(v_b_1178_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_b_1178_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v_b_1178_, 0);
lean_dec(v_unused_1217_);
v___x_1194_ = v_b_1178_;
v_isShared_1195_ = v_isSharedCheck_1216_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_snd_1192_);
lean_dec(v_b_1178_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1216_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_a_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1196_ = lean_array_uget_borrowed(v_as_1175_, v_i_1177_);
v___x_1197_ = lean_box(0);
v___x_1198_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1192_, v_isLower_1174_, v_a_1196_, v___x_1197_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_dec_ref(v___x_1198_);
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_nat_add(v_snd_1192_, v___x_1200_);
lean_dec(v_snd_1192_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v___x_1201_);
lean_ctor_set(v___x_1194_, 0, v___x_1199_);
v___x_1203_ = v___x_1194_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
size_t v___x_1204_; size_t v___x_1205_; 
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = lean_usize_add(v_i_1177_, v___x_1204_);
v_i_1177_ = v___x_1205_;
v_b_1178_ = v___x_1203_;
goto _start;
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_del_object(v___x_1194_);
lean_dec(v_snd_1192_);
v_a_1208_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1198_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1198_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object* v_isLower_1218_, lean_object* v_as_1219_, lean_object* v_sz_1220_, lean_object* v_i_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v_isLower_boxed_1234_; size_t v_sz_boxed_1235_; size_t v_i_boxed_1236_; lean_object* v_res_1237_; 
v_isLower_boxed_1234_ = lean_unbox(v_isLower_1218_);
v_sz_boxed_1235_ = lean_unbox_usize(v_sz_1220_);
lean_dec(v_sz_1220_);
v_i_boxed_1236_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1234_, v_as_1219_, v_sz_boxed_1235_, v_i_boxed_1236_, v_b_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v_as_1219_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1238_, lean_object* v_as_1239_, size_t v_sz_1240_, size_t v_i_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_lt(v_i_1241_, v_sz_1240_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_b_1242_);
return v___x_1255_;
}
else
{
lean_object* v_snd_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1280_; 
v_snd_1256_ = lean_ctor_get(v_b_1242_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_b_1242_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v_b_1242_, 0);
lean_dec(v_unused_1281_);
v___x_1258_ = v_b_1242_;
v_isShared_1259_ = v_isSharedCheck_1280_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_snd_1256_);
lean_dec(v_b_1242_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1280_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_a_1260_ = lean_array_uget_borrowed(v_as_1239_, v_i_1241_);
v___x_1261_ = lean_box(0);
v___x_1262_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1256_, v_isLower_1238_, v_a_1260_, v___x_1261_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_dec_ref(v___x_1262_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_add(v_snd_1256_, v___x_1264_);
lean_dec(v_snd_1256_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1265_);
lean_ctor_set(v___x_1258_, 0, v___x_1263_);
v___x_1267_ = v___x_1258_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_add(v_i_1241_, v___x_1268_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1238_, v_as_1239_, v_sz_1240_, v___x_1269_, v___x_1267_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1270_;
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_del_object(v___x_1258_);
lean_dec(v_snd_1256_);
v_a_1272_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1262_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1262_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object* v_isLower_1282_, lean_object* v_as_1283_, lean_object* v_sz_1284_, lean_object* v_i_1285_, lean_object* v_b_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v_isLower_boxed_1298_; size_t v_sz_boxed_1299_; size_t v_i_boxed_1300_; lean_object* v_res_1301_; 
v_isLower_boxed_1298_ = lean_unbox(v_isLower_1282_);
v_sz_boxed_1299_ = lean_unbox_usize(v_sz_1284_);
lean_dec(v_sz_1284_);
v_i_boxed_1300_ = lean_unbox_usize(v_i_1285_);
lean_dec(v_i_1285_);
v_res_1301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1298_, v_as_1283_, v_sz_boxed_1299_, v_i_boxed_1300_, v_b_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v_as_1283_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(lean_object* v_init_1302_, uint8_t v_isLower_1303_, lean_object* v_n_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
if (lean_obj_tag(v_n_1304_) == 0)
{
lean_object* v_cs_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; size_t v_sz_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v_cs_1317_ = lean_ctor_get(v_n_1304_, 0);
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v_b_1305_);
v_sz_1320_ = lean_array_size(v_cs_1317_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1302_, v_isLower_1303_, v_cs_1317_, v_sz_1320_, v___x_1321_, v___x_1319_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1337_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1337_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1337_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v_fst_1327_; 
v_fst_1327_ = lean_ctor_get(v_a_1323_, 0);
if (lean_obj_tag(v_fst_1327_) == 0)
{
lean_object* v_snd_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v_snd_1328_ = lean_ctor_get(v_a_1323_, 1);
lean_inc(v_snd_1328_);
lean_dec(v_a_1323_);
v___x_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_snd_1328_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1329_);
v___x_1331_ = v___x_1325_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
else
{
lean_object* v_val_1333_; lean_object* v___x_1335_; 
lean_inc_ref(v_fst_1327_);
lean_dec(v_a_1323_);
v_val_1333_ = lean_ctor_get(v_fst_1327_, 0);
lean_inc(v_val_1333_);
lean_dec_ref(v_fst_1327_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v_val_1333_);
v___x_1335_ = v___x_1325_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_val_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1338_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1322_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1322_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_vs_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; size_t v_sz_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v_vs_1346_ = lean_ctor_get(v_n_1304_, 0);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_b_1305_);
v_sz_1349_ = lean_array_size(v_vs_1346_);
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1303_, v_vs_1346_, v_sz_1349_, v___x_1350_, v___x_1348_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1366_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1366_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1366_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_fst_1356_; 
v_fst_1356_ = lean_ctor_get(v_a_1352_, 0);
if (lean_obj_tag(v_fst_1356_) == 0)
{
lean_object* v_snd_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v_snd_1357_ = lean_ctor_get(v_a_1352_, 1);
lean_inc(v_snd_1357_);
lean_dec(v_a_1352_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_snd_1357_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1358_);
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v_val_1362_; lean_object* v___x_1364_; 
lean_inc_ref(v_fst_1356_);
lean_dec(v_a_1352_);
v_val_1362_ = lean_ctor_get(v_fst_1356_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v_fst_1356_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_val_1362_);
v___x_1364_ = v___x_1354_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_val_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1367_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1351_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1351_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object* v_init_1375_, uint8_t v_isLower_1376_, lean_object* v_as_1377_, size_t v_sz_1378_, size_t v_i_1379_, lean_object* v_b_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_usize_dec_lt(v_i_1379_, v_sz_1378_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_b_1380_);
return v___x_1393_;
}
else
{
lean_object* v_snd_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1428_; 
v_snd_1394_ = lean_ctor_get(v_b_1380_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_b_1380_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_b_1380_, 0);
lean_dec(v_unused_1429_);
v___x_1396_ = v_b_1380_;
v_isShared_1397_ = v_isSharedCheck_1428_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_snd_1394_);
lean_dec(v_b_1380_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1428_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_a_1398_; lean_object* v___x_1399_; 
v_a_1398_ = lean_array_uget_borrowed(v_as_1377_, v_i_1379_);
lean_inc(v_snd_1394_);
v___x_1399_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1375_, v_isLower_1376_, v_a_1398_, v_snd_1394_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1419_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1419_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1419_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
if (lean_obj_tag(v_a_1400_) == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_a_1400_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1404_);
v___x_1406_ = v___x_1396_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_snd_1394_);
v___x_1406_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1406_);
v___x_1408_ = v___x_1402_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_del_object(v___x_1402_);
lean_dec(v_snd_1394_);
v_a_1411_ = lean_ctor_get(v_a_1400_, 0);
lean_inc(v_a_1411_);
lean_dec_ref(v_a_1400_);
v___x_1412_ = lean_box(0);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 1, v_a_1411_);
lean_ctor_set(v___x_1396_, 0, v___x_1412_);
v___x_1414_ = v___x_1396_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_a_1411_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
size_t v___x_1415_; size_t v___x_1416_; 
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1379_, v___x_1415_);
v_i_1379_ = v___x_1416_;
v_b_1380_ = v___x_1414_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_del_object(v___x_1396_);
lean_dec(v_snd_1394_);
v_a_1420_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1399_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1399_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_init_1430_ = _args[0];
lean_object* v_isLower_1431_ = _args[1];
lean_object* v_as_1432_ = _args[2];
lean_object* v_sz_1433_ = _args[3];
lean_object* v_i_1434_ = _args[4];
lean_object* v_b_1435_ = _args[5];
lean_object* v___y_1436_ = _args[6];
lean_object* v___y_1437_ = _args[7];
lean_object* v___y_1438_ = _args[8];
lean_object* v___y_1439_ = _args[9];
lean_object* v___y_1440_ = _args[10];
lean_object* v___y_1441_ = _args[11];
lean_object* v___y_1442_ = _args[12];
lean_object* v___y_1443_ = _args[13];
lean_object* v___y_1444_ = _args[14];
lean_object* v___y_1445_ = _args[15];
lean_object* v___y_1446_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1447_; size_t v_sz_boxed_1448_; size_t v_i_boxed_1449_; lean_object* v_res_1450_; 
v_isLower_boxed_1447_ = lean_unbox(v_isLower_1431_);
v_sz_boxed_1448_ = lean_unbox_usize(v_sz_1433_);
lean_dec(v_sz_1433_);
v_i_boxed_1449_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1430_, v_isLower_boxed_1447_, v_as_1432_, v_sz_boxed_1448_, v_i_boxed_1449_, v_b_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v_as_1432_);
lean_dec(v_init_1430_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_init_1451_, lean_object* v_isLower_1452_, lean_object* v_n_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_isLower_boxed_1466_; lean_object* v_res_1467_; 
v_isLower_boxed_1466_ = lean_unbox(v_isLower_1452_);
v_res_1467_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1451_, v_isLower_boxed_1466_, v_n_1453_, v_b_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v_n_1453_);
lean_dec(v_init_1451_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(uint8_t v_isLower_1468_, lean_object* v_t_1469_, lean_object* v_init_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_root_1482_; lean_object* v_tail_1483_; lean_object* v___x_1484_; 
v_root_1482_ = lean_ctor_get(v_t_1469_, 0);
v_tail_1483_ = lean_ctor_get(v_t_1469_, 1);
lean_inc(v_init_1470_);
v___x_1484_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1470_, v_isLower_1468_, v_root_1482_, v_init_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v_init_1470_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1521_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1521_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1521_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
if (lean_obj_tag(v_a_1485_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1491_; 
v_a_1489_ = lean_ctor_get(v_a_1485_, 0);
lean_inc(v_a_1489_);
lean_dec_ref(v_a_1485_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v_a_1489_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; size_t v_sz_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
lean_del_object(v___x_1487_);
v_a_1493_ = lean_ctor_get(v_a_1485_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v_a_1485_);
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v_a_1493_);
v_sz_1496_ = lean_array_size(v_tail_1483_);
v___x_1497_ = ((size_t)0ULL);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_1468_, v_tail_1483_, v_sz_1496_, v___x_1497_, v___x_1495_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1512_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1512_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1512_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_fst_1503_; 
v_fst_1503_ = lean_ctor_get(v_a_1499_, 0);
if (lean_obj_tag(v_fst_1503_) == 0)
{
lean_object* v_snd_1504_; lean_object* v___x_1506_; 
v_snd_1504_ = lean_ctor_get(v_a_1499_, 1);
lean_inc(v_snd_1504_);
lean_dec(v_a_1499_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v_snd_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_snd_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
else
{
lean_object* v_val_1508_; lean_object* v___x_1510_; 
lean_inc_ref(v_fst_1503_);
lean_dec(v_a_1499_);
v_val_1508_ = lean_ctor_get(v_fst_1503_, 0);
lean_inc(v_val_1508_);
lean_dec_ref(v_fst_1503_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v_val_1508_);
v___x_1510_ = v___x_1501_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_val_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_a_1513_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1498_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1498_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_a_1522_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1484_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1484_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1530_, lean_object* v_t_1531_, lean_object* v_init_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
uint8_t v_isLower_boxed_1544_; lean_object* v_res_1545_; 
v_isLower_boxed_1544_ = lean_unbox(v_isLower_1530_);
v_res_1545_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_boxed_1544_, v_t_1531_, v_init_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v_t_1531_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(lean_object* v_css_1546_, uint8_t v_isLower_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_x_1559_; lean_object* v___x_1560_; 
v_x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_1547_, v_css_1546_, v_x_1559_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v___x_1560_, 0);
lean_dec(v_unused_1569_);
v___x_1562_ = v___x_1560_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v___x_1560_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_box(0);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
v_a_1570_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1560_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1560_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs___boxed(lean_object* v_css_1578_, lean_object* v_isLower_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
uint8_t v_isLower_boxed_1591_; lean_object* v_res_1592_; 
v_isLower_boxed_1591_ = lean_unbox(v_isLower_1579_);
v_res_1592_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_css_1578_, v_isLower_boxed_1591_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_css_1578_);
return v_res_1592_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1595_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1));
v___x_1596_ = lean_unsigned_to_nat(2u);
v___x_1597_ = lean_unsigned_to_nat(55u);
v___x_1598_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0));
v___x_1599_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_1600_ = l_mkPanicMessageWithDecl(v___x_1599_, v___x_1598_, v___x_1597_, v___x_1596_, v___x_1595_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1601_, v_a_1609_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v_lowers_1614_; lean_object* v_vars_1615_; lean_object* v_size_1616_; lean_object* v_size_1617_; uint8_t v___x_1618_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref(v___x_1612_);
v_lowers_1614_ = lean_ctor_get(v_a_1613_, 7);
lean_inc_ref(v_lowers_1614_);
v_vars_1615_ = lean_ctor_get(v_a_1613_, 0);
lean_inc_ref(v_vars_1615_);
lean_dec(v_a_1613_);
v_size_1616_ = lean_ctor_get(v_lowers_1614_, 2);
v_size_1617_ = lean_ctor_get(v_vars_1615_, 2);
lean_inc(v_size_1617_);
lean_dec_ref(v_vars_1615_);
v___x_1618_ = lean_nat_dec_eq(v_size_1616_, v_size_1617_);
lean_dec(v_size_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec_ref(v_lowers_1614_);
v___x_1619_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2);
v___x_1620_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_1619_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_lowers_1614_, v___x_1618_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
lean_dec_ref(v_lowers_1614_);
return v___x_1621_;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1612_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1612_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___boxed(lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec(v_a_1630_);
return v_res_1641_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1644_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1));
v___x_1645_ = lean_unsigned_to_nat(2u);
v___x_1646_ = lean_unsigned_to_nat(60u);
v___x_1647_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0));
v___x_1648_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_1649_ = l_mkPanicMessageWithDecl(v___x_1648_, v___x_1647_, v___x_1646_, v___x_1645_, v___x_1644_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1650_, v_a_1658_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v_uppers_1663_; lean_object* v_vars_1664_; lean_object* v_size_1665_; lean_object* v_size_1666_; uint8_t v___x_1667_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref(v___x_1661_);
v_uppers_1663_ = lean_ctor_get(v_a_1662_, 8);
lean_inc_ref(v_uppers_1663_);
v_vars_1664_ = lean_ctor_get(v_a_1662_, 0);
lean_inc_ref(v_vars_1664_);
lean_dec(v_a_1662_);
v_size_1665_ = lean_ctor_get(v_uppers_1663_, 2);
v_size_1666_ = lean_ctor_get(v_vars_1664_, 2);
lean_inc(v_size_1666_);
lean_dec_ref(v_vars_1664_);
v___x_1667_ = lean_nat_dec_eq(v_size_1665_, v_size_1666_);
lean_dec(v_size_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v_uppers_1663_);
v___x_1668_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2);
v___x_1669_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_1668_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
return v___x_1669_;
}
else
{
uint8_t v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = 0;
v___x_1671_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_uppers_1663_, v___x_1670_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
lean_dec_ref(v_uppers_1663_);
return v___x_1671_;
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_a_1672_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1661_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1661_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___boxed(lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec(v_a_1680_);
return v_res_1691_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(lean_object* v_msg_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_4873__overap_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0);
v___x_4873__overap_1706_ = lean_panic_fn_borrowed(v___x_1705_, v_msg_1693_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc(v___y_1694_);
v___x_1707_ = lean_apply_11(v___x_4873__overap_1706_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, lean_box(0));
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___boxed(lean_object* v_msg_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v_msg_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec(v___y_1709_);
return v_res_1720_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_nat_to_int(v___x_1721_);
return v___x_1722_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2));
v___x_1726_ = lean_unsigned_to_nat(6u);
v___x_1727_ = lean_unsigned_to_nat(70u);
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_1729_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_1730_ = l_mkPanicMessageWithDecl(v___x_1729_, v___x_1728_, v___x_1727_, v___x_1726_, v___x_1725_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1731_, size_t v_sz_1732_, size_t v_i_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v___x_1746_; 
v___x_1746_ = lean_usize_dec_lt(v_i_1733_, v_sz_1732_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_b_1734_);
return v___x_1747_;
}
else
{
lean_object* v_snd_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1806_; 
v_snd_1748_ = lean_ctor_get(v_b_1734_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_b_1734_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_b_1734_, 0);
lean_dec(v_unused_1807_);
v___x_1750_ = v_b_1734_;
v_isShared_1751_ = v_isSharedCheck_1806_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snd_1748_);
lean_dec(v_b_1734_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1806_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v_a_1754_; lean_object* v_a_1764_; 
v___x_1752_ = lean_box(0);
v_a_1764_ = lean_array_uget(v_as_1731_, v_i_1733_);
if (lean_obj_tag(v_a_1764_) == 1)
{
lean_object* v_val_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1805_; 
v_val_1765_ = lean_ctor_get(v_a_1764_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_a_1764_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1767_ = v_a_1764_;
v_isShared_1768_ = v_isSharedCheck_1805_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_val_1765_);
lean_dec(v_a_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1805_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_d_1769_; lean_object* v_p_1770_; lean_object* v___x_1771_; 
v_d_1769_ = lean_ctor_get(v_val_1765_, 0);
lean_inc(v_d_1769_);
v_p_1770_ = lean_ctor_get(v_val_1765_, 1);
lean_inc_ref(v_p_1770_);
lean_dec(v_val_1765_);
v___x_1771_ = l_Int_Linear_Poly_checkCnstrOf(v_p_1770_, v_snd_1748_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec_ref(v_p_1770_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
lean_dec_ref(v___x_1771_);
v___x_1772_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1773_ = lean_int_dec_lt(v___x_1772_, v_d_1769_);
lean_dec(v_d_1769_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1775_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1774_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1788_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1788_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1788_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
if (lean_obj_tag(v_a_1776_) == 0)
{
lean_object* v___x_1781_; 
lean_del_object(v___x_1750_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v_a_1776_);
v___x_1781_ = v___x_1767_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v_snd_1748_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1782_);
v___x_1784_ = v___x_1778_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; 
lean_del_object(v___x_1778_);
lean_del_object(v___x_1767_);
lean_dec(v_snd_1748_);
v_a_1787_ = lean_ctor_get(v_a_1776_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v_a_1776_);
v_a_1754_ = v_a_1787_;
goto v___jp_1753_;
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_del_object(v___x_1767_);
lean_del_object(v___x_1750_);
lean_dec(v_snd_1748_);
v_a_1789_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1775_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1775_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_del_object(v___x_1767_);
goto v___jp_1761_;
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_d_1769_);
lean_del_object(v___x_1767_);
lean_del_object(v___x_1750_);
lean_dec(v_snd_1748_);
v_a_1797_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1771_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1771_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
else
{
lean_dec(v_a_1764_);
goto v___jp_1761_;
}
v___jp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v_a_1754_);
lean_ctor_set(v___x_1750_, 0, v___x_1752_);
v___x_1756_ = v___x_1750_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_a_1754_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
size_t v___x_1757_; size_t v___x_1758_; 
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1733_, v___x_1757_);
v_i_1733_ = v___x_1758_;
v_b_1734_ = v___x_1756_;
goto _start;
}
}
v___jp_1761_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_snd_1748_, v___x_1762_);
lean_dec(v_snd_1748_);
v_a_1754_ = v___x_1763_;
goto v___jp_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1808_, lean_object* v_sz_1809_, lean_object* v_i_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
size_t v_sz_boxed_1823_; size_t v_i_boxed_1824_; lean_object* v_res_1825_; 
v_sz_boxed_1823_ = lean_unbox_usize(v_sz_1809_);
lean_dec(v_sz_1809_);
v_i_boxed_1824_ = lean_unbox_usize(v_i_1810_);
lean_dec(v_i_1810_);
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1808_, v_sz_boxed_1823_, v_i_boxed_1824_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v_as_1808_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(lean_object* v_as_1826_, size_t v_sz_1827_, size_t v_i_1828_, lean_object* v_b_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_usize_dec_lt(v_i_1828_, v_sz_1827_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_b_1829_);
return v___x_1842_;
}
else
{
lean_object* v_snd_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1901_; 
v_snd_1843_ = lean_ctor_get(v_b_1829_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_b_1829_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v_b_1829_, 0);
lean_dec(v_unused_1902_);
v___x_1845_ = v_b_1829_;
v_isShared_1846_ = v_isSharedCheck_1901_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_snd_1843_);
lean_dec(v_b_1829_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1901_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v_a_1849_; lean_object* v_a_1859_; 
v___x_1847_ = lean_box(0);
v_a_1859_ = lean_array_uget(v_as_1826_, v_i_1828_);
if (lean_obj_tag(v_a_1859_) == 1)
{
lean_object* v_val_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1900_; 
v_val_1860_ = lean_ctor_get(v_a_1859_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_a_1859_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1862_ = v_a_1859_;
v_isShared_1863_ = v_isSharedCheck_1900_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_val_1860_);
lean_dec(v_a_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1900_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_d_1864_; lean_object* v_p_1865_; lean_object* v___x_1866_; 
v_d_1864_ = lean_ctor_get(v_val_1860_, 0);
lean_inc(v_d_1864_);
v_p_1865_ = lean_ctor_get(v_val_1860_, 1);
lean_inc_ref(v_p_1865_);
lean_dec(v_val_1860_);
v___x_1866_ = l_Int_Linear_Poly_checkCnstrOf(v_p_1865_, v_snd_1843_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec_ref(v_p_1865_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
lean_dec_ref(v___x_1866_);
v___x_1867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1868_ = lean_int_dec_lt(v___x_1867_, v_d_1864_);
lean_dec(v_d_1864_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1870_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1869_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1883_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1883_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1883_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
if (lean_obj_tag(v_a_1871_) == 0)
{
lean_object* v___x_1876_; 
lean_del_object(v___x_1845_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v_a_1871_);
v___x_1876_ = v___x_1862_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v_snd_1843_);
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
}
else
{
lean_object* v_a_1882_; 
lean_del_object(v___x_1873_);
lean_del_object(v___x_1862_);
lean_dec(v_snd_1843_);
v_a_1882_ = lean_ctor_get(v_a_1871_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v_a_1871_);
v_a_1849_ = v_a_1882_;
goto v___jp_1848_;
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_del_object(v___x_1862_);
lean_del_object(v___x_1845_);
lean_dec(v_snd_1843_);
v_a_1884_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1870_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1870_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_del_object(v___x_1862_);
goto v___jp_1856_;
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v_d_1864_);
lean_del_object(v___x_1862_);
lean_del_object(v___x_1845_);
lean_dec(v_snd_1843_);
v_a_1892_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1866_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1866_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_dec(v_a_1859_);
goto v___jp_1856_;
}
v___jp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v_a_1849_);
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1851_ = v___x_1845_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_a_1849_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
size_t v___x_1852_; size_t v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = ((size_t)1ULL);
v___x_1853_ = lean_usize_add(v_i_1828_, v___x_1852_);
v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1826_, v_sz_1827_, v___x_1853_, v___x_1851_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
return v___x_1854_;
}
}
v___jp_1856_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_unsigned_to_nat(1u);
v___x_1858_ = lean_nat_add(v_snd_1843_, v___x_1857_);
lean_dec(v_snd_1843_);
v_a_1849_ = v___x_1858_;
goto v___jp_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1903_, lean_object* v_sz_1904_, lean_object* v_i_1905_, lean_object* v_b_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
size_t v_sz_boxed_1918_; size_t v_i_boxed_1919_; lean_object* v_res_1920_; 
v_sz_boxed_1918_ = lean_unbox_usize(v_sz_1904_);
lean_dec(v_sz_1904_);
v_i_boxed_1919_ = lean_unbox_usize(v_i_1905_);
lean_dec(v_i_1905_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_as_1903_, v_sz_boxed_1918_, v_i_boxed_1919_, v_b_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v_as_1903_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(lean_object* v_init_1921_, lean_object* v_n_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
if (lean_obj_tag(v_n_1922_) == 0)
{
lean_object* v_cs_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; size_t v_sz_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v_cs_1935_ = lean_ctor_get(v_n_1922_, 0);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v_b_1923_);
v_sz_1938_ = lean_array_size(v_cs_1935_);
v___x_1939_ = ((size_t)0ULL);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_1921_, v_cs_1935_, v_sz_1938_, v___x_1939_, v___x_1937_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1955_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1955_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1955_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v_fst_1945_; 
v_fst_1945_ = lean_ctor_get(v_a_1941_, 0);
if (lean_obj_tag(v_fst_1945_) == 0)
{
lean_object* v_snd_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v_snd_1946_ = lean_ctor_get(v_a_1941_, 1);
lean_inc(v_snd_1946_);
lean_dec(v_a_1941_);
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_snd_1946_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1947_);
v___x_1949_ = v___x_1943_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
else
{
lean_object* v_val_1951_; lean_object* v___x_1953_; 
lean_inc_ref(v_fst_1945_);
lean_dec(v_a_1941_);
v_val_1951_ = lean_ctor_get(v_fst_1945_, 0);
lean_inc(v_val_1951_);
lean_dec_ref(v_fst_1945_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v_val_1951_);
v___x_1953_ = v___x_1943_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_val_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
v_a_1956_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1940_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1940_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_vs_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; size_t v_sz_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v_vs_1964_ = lean_ctor_get(v_n_1922_, 0);
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v_b_1923_);
v_sz_1967_ = lean_array_size(v_vs_1964_);
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_vs_1964_, v_sz_1967_, v___x_1968_, v___x_1966_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1984_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1984_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1984_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_fst_1974_; 
v_fst_1974_ = lean_ctor_get(v_a_1970_, 0);
if (lean_obj_tag(v_fst_1974_) == 0)
{
lean_object* v_snd_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v_snd_1975_ = lean_ctor_get(v_a_1970_, 1);
lean_inc(v_snd_1975_);
lean_dec(v_a_1970_);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_snd_1975_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1976_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
else
{
lean_object* v_val_1980_; lean_object* v___x_1982_; 
lean_inc_ref(v_fst_1974_);
lean_dec(v_a_1970_);
v_val_1980_ = lean_ctor_get(v_fst_1974_, 0);
lean_inc(v_val_1980_);
lean_dec_ref(v_fst_1974_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_val_1980_);
v___x_1982_ = v___x_1972_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_val_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
v_a_1985_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1969_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1969_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(lean_object* v_init_1993_, lean_object* v_as_1994_, size_t v_sz_1995_, size_t v_i_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_b_1997_);
return v___x_2010_;
}
else
{
lean_object* v_snd_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2045_; 
v_snd_2011_ = lean_ctor_get(v_b_1997_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_b_1997_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_b_1997_, 0);
lean_dec(v_unused_2046_);
v___x_2013_ = v_b_1997_;
v_isShared_2014_ = v_isSharedCheck_2045_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_snd_2011_);
lean_dec(v_b_1997_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2045_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_array_uget_borrowed(v_as_1994_, v_i_1996_);
lean_inc(v_snd_2011_);
v___x_2016_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_1993_, v_a_2015_, v_snd_2011_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2036_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2036_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2036_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
if (lean_obj_tag(v_a_2017_) == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2017_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2021_);
v___x_2023_ = v___x_2013_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_snd_2011_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2023_);
v___x_2025_ = v___x_2019_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
lean_del_object(v___x_2019_);
lean_dec(v_snd_2011_);
v_a_2028_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v_a_2017_);
v___x_2029_ = lean_box(0);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v_a_2028_);
lean_ctor_set(v___x_2013_, 0, v___x_2029_);
v___x_2031_ = v___x_2013_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_a_2028_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
size_t v___x_2032_; size_t v___x_2033_; 
v___x_2032_ = ((size_t)1ULL);
v___x_2033_ = lean_usize_add(v_i_1996_, v___x_2032_);
v_i_1996_ = v___x_2033_;
v_b_1997_ = v___x_2031_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_del_object(v___x_2013_);
lean_dec(v_snd_2011_);
v_a_2037_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2016_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2016_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2___boxed(lean_object* v_init_2047_, lean_object* v_as_2048_, lean_object* v_sz_2049_, lean_object* v_i_2050_, lean_object* v_b_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
size_t v_sz_boxed_2063_; size_t v_i_boxed_2064_; lean_object* v_res_2065_; 
v_sz_boxed_2063_ = lean_unbox_usize(v_sz_2049_);
lean_dec(v_sz_2049_);
v_i_boxed_2064_ = lean_unbox_usize(v_i_2050_);
lean_dec(v_i_2050_);
v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_2047_, v_as_2048_, v_sz_boxed_2063_, v_i_boxed_2064_, v_b_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v_as_2048_);
lean_dec(v_init_2047_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1___boxed(lean_object* v_init_2066_, lean_object* v_n_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2066_, v_n_2067_, v_b_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v_n_2067_);
lean_dec(v_init_2066_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(lean_object* v_as_2081_, size_t v_sz_2082_, size_t v_i_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_lt(v_i_2083_, v_sz_2082_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_b_2084_);
return v___x_2097_;
}
else
{
lean_object* v_snd_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2157_; 
v_snd_2098_ = lean_ctor_get(v_b_2084_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_b_2084_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v_b_2084_, 0);
lean_dec(v_unused_2158_);
v___x_2100_ = v_b_2084_;
v_isShared_2101_ = v_isSharedCheck_2157_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_snd_2098_);
lean_dec(v_b_2084_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2157_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v_a_2104_; lean_object* v_a_2114_; 
v___x_2102_ = lean_box(0);
v_a_2114_ = lean_array_uget(v_as_2081_, v_i_2083_);
if (lean_obj_tag(v_a_2114_) == 1)
{
lean_object* v_val_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2156_; 
v_val_2115_ = lean_ctor_get(v_a_2114_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_a_2114_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2117_ = v_a_2114_;
v_isShared_2118_ = v_isSharedCheck_2156_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_val_2115_);
lean_dec(v_a_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2156_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v_d_2119_; lean_object* v_p_2120_; lean_object* v___x_2121_; 
v_d_2119_ = lean_ctor_get(v_val_2115_, 0);
lean_inc(v_d_2119_);
v_p_2120_ = lean_ctor_get(v_val_2115_, 1);
lean_inc_ref(v_p_2120_);
lean_dec(v_val_2115_);
v___x_2121_ = l_Int_Linear_Poly_checkCnstrOf(v_p_2120_, v_snd_2098_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec_ref(v_p_2120_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
lean_dec_ref(v___x_2121_);
v___x_2122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2123_ = lean_int_dec_lt(v___x_2122_, v_d_2119_);
lean_dec(v_d_2119_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2125_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2124_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2139_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2139_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2139_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
if (lean_obj_tag(v_a_2126_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; 
lean_del_object(v___x_2100_);
v_a_2130_ = lean_ctor_get(v_a_2126_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v_a_2126_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v_a_2130_);
v___x_2132_ = v___x_2117_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2130_);
v___x_2132_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v_snd_2098_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2133_);
v___x_2135_ = v___x_2128_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
else
{
lean_object* v_a_2138_; 
lean_del_object(v___x_2128_);
lean_del_object(v___x_2117_);
lean_dec(v_snd_2098_);
v_a_2138_ = lean_ctor_get(v_a_2126_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v_a_2126_);
v_a_2104_ = v_a_2138_;
goto v___jp_2103_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_del_object(v___x_2117_);
lean_del_object(v___x_2100_);
lean_dec(v_snd_2098_);
v_a_2140_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2125_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2125_);
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
else
{
lean_del_object(v___x_2117_);
goto v___jp_2111_;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_d_2119_);
lean_del_object(v___x_2117_);
lean_del_object(v___x_2100_);
lean_dec(v_snd_2098_);
v_a_2148_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2121_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2121_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
lean_dec(v_a_2114_);
goto v___jp_2111_;
}
v___jp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 1, v_a_2104_);
lean_ctor_set(v___x_2100_, 0, v___x_2102_);
v___x_2106_ = v___x_2100_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_a_2104_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
size_t v___x_2107_; size_t v___x_2108_; 
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_add(v_i_2083_, v___x_2107_);
v_i_2083_ = v___x_2108_;
v_b_2084_ = v___x_2106_;
goto _start;
}
}
v___jp_2111_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_unsigned_to_nat(1u);
v___x_2113_ = lean_nat_add(v_snd_2098_, v___x_2112_);
lean_dec(v_snd_2098_);
v_a_2104_ = v___x_2113_;
goto v___jp_2103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2159_, lean_object* v_sz_2160_, lean_object* v_i_2161_, lean_object* v_b_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
size_t v_sz_boxed_2174_; size_t v_i_boxed_2175_; lean_object* v_res_2176_; 
v_sz_boxed_2174_ = lean_unbox_usize(v_sz_2160_);
lean_dec(v_sz_2160_);
v_i_boxed_2175_ = lean_unbox_usize(v_i_2161_);
lean_dec(v_i_2161_);
v_res_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2159_, v_sz_boxed_2174_, v_i_boxed_2175_, v_b_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v_as_2159_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(lean_object* v_as_2177_, size_t v_sz_2178_, size_t v_i_2179_, lean_object* v_b_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
uint8_t v___x_2192_; 
v___x_2192_ = lean_usize_dec_lt(v_i_2179_, v_sz_2178_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_b_2180_);
return v___x_2193_;
}
else
{
lean_object* v_snd_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2253_; 
v_snd_2194_ = lean_ctor_get(v_b_2180_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_b_2180_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v_b_2180_, 0);
lean_dec(v_unused_2254_);
v___x_2196_ = v_b_2180_;
v_isShared_2197_ = v_isSharedCheck_2253_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_snd_2194_);
lean_dec(v_b_2180_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2253_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v_a_2200_; lean_object* v_a_2210_; 
v___x_2198_ = lean_box(0);
v_a_2210_ = lean_array_uget(v_as_2177_, v_i_2179_);
if (lean_obj_tag(v_a_2210_) == 1)
{
lean_object* v_val_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2252_; 
v_val_2211_ = lean_ctor_get(v_a_2210_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_a_2210_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2213_ = v_a_2210_;
v_isShared_2214_ = v_isSharedCheck_2252_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_val_2211_);
lean_dec(v_a_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2252_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_d_2215_; lean_object* v_p_2216_; lean_object* v___x_2217_; 
v_d_2215_ = lean_ctor_get(v_val_2211_, 0);
lean_inc(v_d_2215_);
v_p_2216_ = lean_ctor_get(v_val_2211_, 1);
lean_inc_ref(v_p_2216_);
lean_dec(v_val_2211_);
v___x_2217_ = l_Int_Linear_Poly_checkCnstrOf(v_p_2216_, v_snd_2194_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec_ref(v_p_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
lean_dec_ref(v___x_2217_);
v___x_2218_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2219_ = lean_int_dec_lt(v___x_2218_, v_d_2215_);
lean_dec(v_d_2215_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2221_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2220_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2235_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2235_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2235_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; 
lean_del_object(v___x_2196_);
v_a_2226_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2226_);
lean_dec_ref(v_a_2222_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_a_2226_);
v___x_2228_ = v___x_2213_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2226_);
v___x_2228_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v_snd_2194_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2229_);
v___x_2231_ = v___x_2224_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
lean_object* v_a_2234_; 
lean_del_object(v___x_2224_);
lean_del_object(v___x_2213_);
lean_dec(v_snd_2194_);
v_a_2234_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2234_);
lean_dec_ref(v_a_2222_);
v_a_2200_ = v_a_2234_;
goto v___jp_2199_;
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_del_object(v___x_2213_);
lean_del_object(v___x_2196_);
lean_dec(v_snd_2194_);
v_a_2236_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2221_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2221_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_del_object(v___x_2213_);
goto v___jp_2207_;
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_d_2215_);
lean_del_object(v___x_2213_);
lean_del_object(v___x_2196_);
lean_dec(v_snd_2194_);
v_a_2244_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2217_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2217_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_dec(v_a_2210_);
goto v___jp_2207_;
}
v___jp_2199_:
{
lean_object* v___x_2202_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v_a_2200_);
lean_ctor_set(v___x_2196_, 0, v___x_2198_);
v___x_2202_ = v___x_2196_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_a_2200_);
v___x_2202_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
size_t v___x_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = ((size_t)1ULL);
v___x_2204_ = lean_usize_add(v_i_2179_, v___x_2203_);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2177_, v_sz_2178_, v___x_2204_, v___x_2202_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
return v___x_2205_;
}
}
v___jp_2207_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_add(v_snd_2194_, v___x_2208_);
lean_dec(v_snd_2194_);
v_a_2200_ = v___x_2209_;
goto v___jp_2199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2___boxed(lean_object* v_as_2255_, lean_object* v_sz_2256_, lean_object* v_i_2257_, lean_object* v_b_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
size_t v_sz_boxed_2270_; size_t v_i_boxed_2271_; lean_object* v_res_2272_; 
v_sz_boxed_2270_ = lean_unbox_usize(v_sz_2256_);
lean_dec(v_sz_2256_);
v_i_boxed_2271_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_as_2255_, v_sz_boxed_2270_, v_i_boxed_2271_, v_b_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v_as_2255_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(lean_object* v_t_2273_, lean_object* v_init_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_root_2286_; lean_object* v_tail_2287_; lean_object* v___x_2288_; 
v_root_2286_ = lean_ctor_get(v_t_2273_, 0);
v_tail_2287_ = lean_ctor_get(v_t_2273_, 1);
lean_inc(v_init_2274_);
v___x_2288_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2274_, v_root_2286_, v_init_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v_init_2274_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2325_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2325_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2325_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
if (lean_obj_tag(v_a_2289_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; 
v_a_2293_ = lean_ctor_get(v_a_2289_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v_a_2289_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v_a_2293_);
v___x_2295_ = v___x_2291_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; size_t v_sz_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
lean_del_object(v___x_2291_);
v_a_2297_ = lean_ctor_get(v_a_2289_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v_a_2289_);
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v_a_2297_);
v_sz_2300_ = lean_array_size(v_tail_2287_);
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_tail_2287_, v_sz_2300_, v___x_2301_, v___x_2299_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2316_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2316_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2316_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_fst_2307_; 
v_fst_2307_ = lean_ctor_get(v_a_2303_, 0);
if (lean_obj_tag(v_fst_2307_) == 0)
{
lean_object* v_snd_2308_; lean_object* v___x_2310_; 
v_snd_2308_ = lean_ctor_get(v_a_2303_, 1);
lean_inc(v_snd_2308_);
lean_dec(v_a_2303_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v_snd_2308_);
v___x_2310_ = v___x_2305_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_snd_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
else
{
lean_object* v_val_2312_; lean_object* v___x_2314_; 
lean_inc_ref(v_fst_2307_);
lean_dec(v_a_2303_);
v_val_2312_ = lean_ctor_get(v_fst_2307_, 0);
lean_inc(v_val_2312_);
lean_dec_ref(v_fst_2307_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v_val_2312_);
v___x_2314_ = v___x_2305_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_val_2312_);
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
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
v_a_2317_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2302_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2302_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2288_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2288_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1___boxed(lean_object* v_t_2334_, lean_object* v_init_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_t_2334_, v_init_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v_t_2334_);
return v_res_2347_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0));
v___x_2350_ = lean_unsigned_to_nat(2u);
v___x_2351_ = lean_unsigned_to_nat(65u);
v___x_2352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_2353_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_2354_ = l_mkPanicMessageWithDecl(v___x_2353_, v___x_2352_, v___x_2351_, v___x_2350_, v___x_2349_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2355_, v_a_2363_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v_vars_2368_; lean_object* v_dvds_2369_; lean_object* v_size_2370_; lean_object* v_size_2371_; uint8_t v___x_2372_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref(v___x_2366_);
v_vars_2368_ = lean_ctor_get(v_a_2367_, 0);
lean_inc_ref(v_vars_2368_);
v_dvds_2369_ = lean_ctor_get(v_a_2367_, 6);
lean_inc_ref(v_dvds_2369_);
lean_dec(v_a_2367_);
v_size_2370_ = lean_ctor_get(v_vars_2368_, 2);
lean_inc(v_size_2370_);
lean_dec_ref(v_vars_2368_);
v_size_2371_ = lean_ctor_get(v_dvds_2369_, 2);
v___x_2372_ = lean_nat_dec_eq(v_size_2370_, v_size_2371_);
lean_dec(v_size_2370_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v_dvds_2369_);
v___x_2373_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1);
v___x_2374_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_2373_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2374_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_dvds_2369_, v___x_2375_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec_ref(v_dvds_2369_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2384_; 
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; 
v_unused_2385_ = lean_ctor_get(v___x_2376_, 0);
lean_dec(v_unused_2385_);
v___x_2378_ = v___x_2376_;
v_isShared_2379_ = v_isSharedCheck_2384_;
goto v_resetjp_2377_;
}
else
{
lean_dec(v___x_2376_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2384_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2380_ = lean_box(0);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2380_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
v_a_2386_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2376_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2376_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
v_a_2394_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2366_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2366_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___boxed(lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec(v_a_2402_);
return v_res_2413_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2415_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__3));
v___x_2416_ = lean_unsigned_to_nat(6u);
v___x_2417_ = lean_unsigned_to_nat(81u);
v___x_2418_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2419_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_2420_ = l_mkPanicMessageWithDecl(v___x_2419_, v___x_2418_, v___x_2417_, v___x_2416_, v___x_2415_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2422_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2));
v___x_2423_ = lean_unsigned_to_nat(6u);
v___x_2424_ = lean_unsigned_to_nat(79u);
v___x_2425_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2426_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_2427_ = l_mkPanicMessageWithDecl(v___x_2426_, v___x_2425_, v___x_2424_, v___x_2423_, v___x_2422_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(lean_object* v_vars_2428_, lean_object* v_x_2429_, lean_object* v_____s_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v_size_2449_; uint8_t v___x_2450_; 
v_fst_2447_ = lean_ctor_get(v_x_2429_, 0);
v_snd_2448_ = lean_ctor_get(v_x_2429_, 1);
v_size_2449_ = lean_ctor_get(v_vars_2428_, 2);
v___x_2450_ = lean_nat_dec_lt(v_snd_2448_, v_size_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1);
v___x_2452_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_2451_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_dec_ref(v___x_2452_);
goto v___jp_2442_;
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2461_ = l_Lean_instInhabitedExpr;
v___x_2462_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2461_, v_vars_2428_, v_snd_2448_);
v___x_2463_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2447_, v___x_2462_);
lean_dec(v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3);
v___x_2465_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2464_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
return v___x_2465_;
}
else
{
goto v___jp_2442_;
}
}
v___jp_2442_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = lean_nat_add(v_____s_2430_, v___x_2443_);
v___x_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
return v___x_2446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(lean_object* v_vars_2466_, lean_object* v_x_2467_, lean_object* v_____s_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(v_vars_2466_, v_x_2467_, v_____s_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec(v_____s_2468_);
lean_dec_ref(v_x_2467_);
lean_dec_ref(v_vars_2466_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2481_, lean_object* v_keys_2482_, lean_object* v_vals_2483_, lean_object* v_i_2484_, lean_object* v_acc_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2497_ = lean_array_get_size(v_keys_2482_);
v___x_2498_ = lean_nat_dec_lt(v_i_2484_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec(v_i_2484_);
lean_dec_ref(v_f_2481_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_acc_2485_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
else
{
lean_object* v_k_2501_; lean_object* v_v_2502_; lean_object* v___x_2503_; 
v_k_2501_ = lean_array_fget_borrowed(v_keys_2482_, v_i_2484_);
v_v_2502_ = lean_array_fget_borrowed(v_vals_2483_, v_i_2484_);
lean_inc_ref(v_f_2481_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc(v___y_2486_);
lean_inc(v_v_2502_);
lean_inc(v_k_2501_);
v___x_2503_ = lean_apply_14(v_f_2481_, v_acc_2485_, v_k_2501_, v_v_2502_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, lean_box(0));
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
if (lean_obj_tag(v_a_2504_) == 0)
{
lean_dec_ref(v_a_2504_);
lean_dec(v_i_2484_);
lean_dec_ref(v_f_2481_);
return v___x_2503_;
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v___x_2503_);
v_a_2505_ = lean_ctor_get(v_a_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref(v_a_2504_);
v___x_2506_ = lean_unsigned_to_nat(1u);
v___x_2507_ = lean_nat_add(v_i_2484_, v___x_2506_);
lean_dec(v_i_2484_);
v_i_2484_ = v___x_2507_;
v_acc_2485_ = v_a_2505_;
goto _start;
}
}
else
{
lean_dec(v_i_2484_);
lean_dec_ref(v_f_2481_);
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2509_, lean_object* v_keys_2510_, lean_object* v_vals_2511_, lean_object* v_i_2512_, lean_object* v_acc_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2509_, v_keys_2510_, v_vals_2511_, v_i_2512_, v_acc_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v_vals_2511_);
lean_dec_ref(v_keys_2510_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 0)
{
lean_object* v_es_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2562_; 
v_es_2540_ = lean_ctor_get(v_x_2527_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_x_2527_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2542_ = v_x_2527_;
v_isShared_2543_ = v_isSharedCheck_2562_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_es_2540_);
lean_dec(v_x_2527_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2562_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = lean_array_get_size(v_es_2540_);
v___x_2546_ = lean_nat_dec_lt(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2548_; 
lean_dec_ref(v_es_2540_);
lean_dec_ref(v_f_2526_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set_tag(v___x_2542_, 1);
lean_ctor_set(v___x_2542_, 0, v_x_2528_);
v___x_2548_ = v___x_2542_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_x_2528_);
v___x_2548_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
}
else
{
uint8_t v___x_2551_; 
v___x_2551_ = lean_nat_dec_le(v___x_2545_, v___x_2545_);
if (v___x_2551_ == 0)
{
if (v___x_2546_ == 0)
{
lean_object* v___x_2553_; 
lean_dec_ref(v_es_2540_);
lean_dec_ref(v_f_2526_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set_tag(v___x_2542_, 1);
lean_ctor_set(v___x_2542_, 0, v_x_2528_);
v___x_2553_ = v___x_2542_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_x_2528_);
v___x_2553_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
else
{
size_t v___x_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
lean_del_object(v___x_2542_);
v___x_2556_ = ((size_t)0ULL);
v___x_2557_ = lean_usize_of_nat(v___x_2545_);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2526_, v_es_2540_, v___x_2556_, v___x_2557_, v_x_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec_ref(v_es_2540_);
return v___x_2558_;
}
}
else
{
size_t v___x_2559_; size_t v___x_2560_; lean_object* v___x_2561_; 
lean_del_object(v___x_2542_);
v___x_2559_ = ((size_t)0ULL);
v___x_2560_ = lean_usize_of_nat(v___x_2545_);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2526_, v_es_2540_, v___x_2559_, v___x_2560_, v_x_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec_ref(v_es_2540_);
return v___x_2561_;
}
}
}
}
else
{
lean_object* v_ks_2563_; lean_object* v_vs_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_ks_2563_ = lean_ctor_get(v_x_2527_, 0);
lean_inc_ref(v_ks_2563_);
v_vs_2564_ = lean_ctor_get(v_x_2527_, 1);
lean_inc_ref(v_vs_2564_);
lean_dec_ref(v_x_2527_);
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2526_, v_ks_2563_, v_vs_2564_, v___x_2565_, v_x_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec_ref(v_vs_2564_);
lean_dec_ref(v_ks_2563_);
return v___x_2566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2567_, lean_object* v_as_2568_, size_t v_i_2569_, size_t v_stop_2570_, lean_object* v_b_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_a_2584_; lean_object* v___y_2589_; uint8_t v___x_2592_; 
v___x_2592_ = lean_usize_dec_eq(v_i_2569_, v_stop_2570_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_array_uget_borrowed(v_as_2568_, v_i_2569_);
switch(lean_obj_tag(v___x_2593_))
{
case 0:
{
lean_object* v_key_2594_; lean_object* v_val_2595_; lean_object* v___x_2596_; 
v_key_2594_ = lean_ctor_get(v___x_2593_, 0);
v_val_2595_ = lean_ctor_get(v___x_2593_, 1);
lean_inc_ref(v_f_2567_);
lean_inc(v___y_2581_);
lean_inc_ref(v___y_2580_);
lean_inc(v___y_2579_);
lean_inc_ref(v___y_2578_);
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2576_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
lean_inc(v___y_2573_);
lean_inc(v___y_2572_);
lean_inc(v_val_2595_);
lean_inc(v_key_2594_);
v___x_2596_ = lean_apply_14(v_f_2567_, v_b_2571_, v_key_2594_, v_val_2595_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, lean_box(0));
v___y_2589_ = v___x_2596_;
goto v___jp_2588_;
}
case 1:
{
lean_object* v_node_2597_; lean_object* v___x_2598_; 
v_node_2597_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_node_2597_);
lean_inc_ref(v_f_2567_);
v___x_2598_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2567_, v_node_2597_, v_b_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
v___y_2589_ = v___x_2598_;
goto v___jp_2588_;
}
default: 
{
v_a_2584_ = v_b_2571_;
goto v___jp_2583_;
}
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v_f_2567_);
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_b_2571_);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
v___jp_2583_:
{
size_t v___x_2585_; size_t v___x_2586_; 
v___x_2585_ = ((size_t)1ULL);
v___x_2586_ = lean_usize_add(v_i_2569_, v___x_2585_);
v_i_2569_ = v___x_2586_;
v_b_2571_ = v_a_2584_;
goto _start;
}
v___jp_2588_:
{
if (lean_obj_tag(v___y_2589_) == 0)
{
lean_object* v_a_2590_; 
v_a_2590_ = lean_ctor_get(v___y_2589_, 0);
if (lean_obj_tag(v_a_2590_) == 0)
{
lean_dec_ref(v_f_2567_);
return v___y_2589_;
}
else
{
lean_object* v_a_2591_; 
lean_inc_ref(v_a_2590_);
lean_dec_ref(v___y_2589_);
v_a_2591_ = lean_ctor_get(v_a_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v_a_2590_);
v_a_2584_ = v_a_2591_;
goto v___jp_2583_;
}
}
else
{
lean_dec_ref(v_f_2567_);
return v___y_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2601_, lean_object* v_as_2602_, lean_object* v_i_2603_, lean_object* v_stop_2604_, lean_object* v_b_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
size_t v_i_boxed_2617_; size_t v_stop_boxed_2618_; lean_object* v_res_2619_; 
v_i_boxed_2617_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_stop_boxed_2618_ = lean_unbox_usize(v_stop_2604_);
lean_dec(v_stop_2604_);
v_res_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2601_, v_as_2602_, v_i_boxed_2617_, v_stop_boxed_2618_, v_b_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v_as_2602_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2620_, v_x_2621_, v_x_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec(v___y_2623_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(lean_object* v_f_2635_, lean_object* v_s_2636_, lean_object* v_a_2637_, lean_object* v_b_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v_a_2637_);
lean_ctor_set(v___x_2650_, 1, v_b_2638_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc_ref(v___y_2645_);
lean_inc(v___y_2644_);
lean_inc_ref(v___y_2643_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v___y_2640_);
lean_inc(v___y_2639_);
v___x_2651_ = lean_apply_13(v_f_2635_, v___x_2650_, v_s_2636_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, lean_box(0));
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2678_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2678_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2678_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
if (lean_obj_tag(v_a_2652_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2666_; 
v_a_2656_ = lean_ctor_get(v_a_2652_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_a_2652_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2658_ = v_a_2652_;
v_isShared_2659_ = v_isSharedCheck_2666_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v_a_2652_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2666_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2663_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2661_);
v___x_2663_ = v___x_2654_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2677_; 
v_a_2667_ = lean_ctor_get(v_a_2652_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_a_2652_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2669_ = v_a_2652_;
v_isShared_2670_ = v_isSharedCheck_2677_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v_a_2652_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2677_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2672_);
v___x_2674_ = v___x_2654_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2651_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2651_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed(lean_object* v_f_2687_, lean_object* v_s_2688_, lean_object* v_a_2689_, lean_object* v_b_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(v_f_2687_, v_s_2688_, v_a_2689_, v_b_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec(v___y_2691_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(lean_object* v_map_2703_, lean_object* v_init_2704_, lean_object* v_f_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___f_2717_; lean_object* v___x_2718_; 
v___f_2717_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed), 15, 1);
lean_closure_set(v___f_2717_, 0, v_f_2705_);
lean_inc_ref(v_map_2703_);
v___x_2718_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v___f_2717_, v_map_2703_, v_init_2704_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2727_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2727_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2727_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v_a_2723_; lean_object* v___x_2725_; 
v_a_2723_ = lean_ctor_get(v_a_2719_, 0);
lean_inc(v_a_2723_);
lean_dec(v_a_2719_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v_a_2723_);
v___x_2725_ = v___x_2721_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_a_2728_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2718_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2718_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___boxed(lean_object* v_map_2736_, lean_object* v_init_2737_, lean_object* v_f_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2736_, v_init_2737_, v_f_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v_map_2736_);
return v_res_2750_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2752_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0));
v___x_2753_ = lean_unsigned_to_nat(2u);
v___x_2754_ = lean_unsigned_to_nat(83u);
v___x_2755_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2756_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_2757_ = l_mkPanicMessageWithDecl(v___x_2756_, v___x_2755_, v___x_2754_, v___x_2753_, v___x_2752_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars(lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2758_, v_a_2766_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v_vars_2771_; lean_object* v_varMap_2772_; lean_object* v___f_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref(v___x_2769_);
v_vars_2771_ = lean_ctor_get(v_a_2770_, 0);
lean_inc_ref_n(v_vars_2771_, 2);
v_varMap_2772_ = lean_ctor_get(v_a_2770_, 1);
lean_inc_ref(v_varMap_2772_);
lean_dec(v_a_2770_);
v___f_2773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2773_, 0, v_vars_2771_);
v___x_2774_ = lean_unsigned_to_nat(0u);
v___x_2775_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_varMap_2772_, v___x_2774_, v___f_2773_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
lean_dec_ref(v_varMap_2772_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2788_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2788_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2788_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v_size_2780_; uint8_t v___x_2781_; 
v_size_2780_ = lean_ctor_get(v_vars_2771_, 2);
lean_inc(v_size_2780_);
lean_dec_ref(v_vars_2771_);
v___x_2781_ = lean_nat_dec_eq(v_size_2780_, v_a_2776_);
lean_dec(v_a_2776_);
lean_dec(v_size_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_del_object(v___x_2778_);
v___x_2782_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1);
v___x_2783_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_2782_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
return v___x_2783_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = lean_box(0);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2784_);
v___x_2786_ = v___x_2778_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec_ref(v_vars_2771_);
v_a_2789_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2775_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2775_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
v_a_2797_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___x_2769_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2769_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___boxed(lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec(v_a_2805_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(lean_object* v_00_u03c3_2817_, lean_object* v_00_u03b2_2818_, lean_object* v_map_2819_, lean_object* v_init_2820_, lean_object* v_f_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2819_, v_init_2820_, v_f_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___boxed(lean_object* v_00_u03c3_2834_, lean_object* v_00_u03b2_2835_, lean_object* v_map_2836_, lean_object* v_init_2837_, lean_object* v_f_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(v_00_u03c3_2834_, v_00_u03b2_2835_, v_map_2836_, v_init_2837_, v_f_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v_map_2836_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(lean_object* v_map_2851_, lean_object* v_f_2852_, lean_object* v_init_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2852_, v_map_2851_, v_init_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_map_2866_, lean_object* v_f_2867_, lean_object* v_init_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(v_map_2866_, v_f_2867_, v_init_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec(v___y_2869_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(lean_object* v_00_u03c3_2881_, lean_object* v_00_u03c3_2882_, lean_object* v_00_u03b2_2883_, lean_object* v_map_2884_, lean_object* v_f_2885_, lean_object* v_init_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2885_, v_map_2884_, v_init_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_2899_ = _args[0];
lean_object* v_00_u03c3_2900_ = _args[1];
lean_object* v_00_u03b2_2901_ = _args[2];
lean_object* v_map_2902_ = _args[3];
lean_object* v_f_2903_ = _args[4];
lean_object* v_init_2904_ = _args[5];
lean_object* v___y_2905_ = _args[6];
lean_object* v___y_2906_ = _args[7];
lean_object* v___y_2907_ = _args[8];
lean_object* v___y_2908_ = _args[9];
lean_object* v___y_2909_ = _args[10];
lean_object* v___y_2910_ = _args[11];
lean_object* v___y_2911_ = _args[12];
lean_object* v___y_2912_ = _args[13];
lean_object* v___y_2913_ = _args[14];
lean_object* v___y_2914_ = _args[15];
lean_object* v___y_2915_ = _args[16];
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(v_00_u03c3_2899_, v_00_u03c3_2900_, v_00_u03b2_2901_, v_map_2902_, v_f_2903_, v_init_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec(v___y_2905_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2917_, lean_object* v_00_u03c3_2918_, lean_object* v_00_u03b1_2919_, lean_object* v_00_u03b2_2920_, lean_object* v_f_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2921_, v_x_2922_, v_x_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_2936_ = _args[0];
lean_object* v_00_u03c3_2937_ = _args[1];
lean_object* v_00_u03b1_2938_ = _args[2];
lean_object* v_00_u03b2_2939_ = _args[3];
lean_object* v_f_2940_ = _args[4];
lean_object* v_x_2941_ = _args[5];
lean_object* v_x_2942_ = _args[6];
lean_object* v___y_2943_ = _args[7];
lean_object* v___y_2944_ = _args[8];
lean_object* v___y_2945_ = _args[9];
lean_object* v___y_2946_ = _args[10];
lean_object* v___y_2947_ = _args[11];
lean_object* v___y_2948_ = _args[12];
lean_object* v___y_2949_ = _args[13];
lean_object* v___y_2950_ = _args[14];
lean_object* v___y_2951_ = _args[15];
lean_object* v___y_2952_ = _args[16];
lean_object* v___y_2953_ = _args[17];
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(v_00_u03c3_2936_, v_00_u03c3_2937_, v_00_u03b1_2938_, v_00_u03b2_2939_, v_f_2940_, v_x_2941_, v_x_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec(v___y_2943_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2955_, lean_object* v_00_u03b2_2956_, lean_object* v_00_u03c3_2957_, lean_object* v_00_u03c3_2958_, lean_object* v_f_2959_, lean_object* v_as_2960_, size_t v_i_2961_, size_t v_stop_2962_, lean_object* v_b_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2959_, v_as_2960_, v_i_2961_, v_stop_2962_, v_b_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03b1_2976_ = _args[0];
lean_object* v_00_u03b2_2977_ = _args[1];
lean_object* v_00_u03c3_2978_ = _args[2];
lean_object* v_00_u03c3_2979_ = _args[3];
lean_object* v_f_2980_ = _args[4];
lean_object* v_as_2981_ = _args[5];
lean_object* v_i_2982_ = _args[6];
lean_object* v_stop_2983_ = _args[7];
lean_object* v_b_2984_ = _args[8];
lean_object* v___y_2985_ = _args[9];
lean_object* v___y_2986_ = _args[10];
lean_object* v___y_2987_ = _args[11];
lean_object* v___y_2988_ = _args[12];
lean_object* v___y_2989_ = _args[13];
lean_object* v___y_2990_ = _args[14];
lean_object* v___y_2991_ = _args[15];
lean_object* v___y_2992_ = _args[16];
lean_object* v___y_2993_ = _args[17];
lean_object* v___y_2994_ = _args[18];
lean_object* v___y_2995_ = _args[19];
_start:
{
size_t v_i_boxed_2996_; size_t v_stop_boxed_2997_; lean_object* v_res_2998_; 
v_i_boxed_2996_ = lean_unbox_usize(v_i_2982_);
lean_dec(v_i_2982_);
v_stop_boxed_2997_ = lean_unbox_usize(v_stop_2983_);
lean_dec(v_stop_2983_);
v_res_2998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2976_, v_00_u03b2_2977_, v_00_u03c3_2978_, v_00_u03c3_2979_, v_f_2980_, v_as_2981_, v_i_boxed_2996_, v_stop_boxed_2997_, v_b_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v_as_2981_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2999_, lean_object* v_00_u03c3_3000_, lean_object* v_00_u03b1_3001_, lean_object* v_00_u03b2_3002_, lean_object* v_f_3003_, lean_object* v_keys_3004_, lean_object* v_vals_3005_, lean_object* v_heq_3006_, lean_object* v_i_3007_, lean_object* v_acc_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3003_, v_keys_3004_, v_vals_3005_, v_i_3007_, v_acc_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_3021_ = _args[0];
lean_object* v_00_u03c3_3022_ = _args[1];
lean_object* v_00_u03b1_3023_ = _args[2];
lean_object* v_00_u03b2_3024_ = _args[3];
lean_object* v_f_3025_ = _args[4];
lean_object* v_keys_3026_ = _args[5];
lean_object* v_vals_3027_ = _args[6];
lean_object* v_heq_3028_ = _args[7];
lean_object* v_i_3029_ = _args[8];
lean_object* v_acc_3030_ = _args[9];
lean_object* v___y_3031_ = _args[10];
lean_object* v___y_3032_ = _args[11];
lean_object* v___y_3033_ = _args[12];
lean_object* v___y_3034_ = _args[13];
lean_object* v___y_3035_ = _args[14];
lean_object* v___y_3036_ = _args[15];
lean_object* v___y_3037_ = _args[16];
lean_object* v___y_3038_ = _args[17];
lean_object* v___y_3039_ = _args[18];
lean_object* v___y_3040_ = _args[19];
lean_object* v___y_3041_ = _args[20];
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3021_, v_00_u03c3_3022_, v_00_u03b1_3023_, v_00_u03b2_3024_, v_f_3025_, v_keys_3026_, v_vals_3027_, v_heq_3028_, v_i_3029_, v_acc_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v_vals_3027_);
lean_dec_ref(v_keys_3026_);
return v_res_3042_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(lean_object* v_a_3043_, lean_object* v_x_3044_){
_start:
{
if (lean_obj_tag(v_x_3044_) == 0)
{
uint8_t v___x_3045_; 
v___x_3045_ = 0;
return v___x_3045_;
}
else
{
lean_object* v_head_3046_; lean_object* v_tail_3047_; uint8_t v___x_3048_; 
v_head_3046_ = lean_ctor_get(v_x_3044_, 0);
v_tail_3047_ = lean_ctor_get(v_x_3044_, 1);
v___x_3048_ = lean_nat_dec_eq(v_a_3043_, v_head_3046_);
if (v___x_3048_ == 0)
{
v_x_3044_ = v_tail_3047_;
goto _start;
}
else
{
return v___x_3048_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0___boxed(lean_object* v_a_3050_, lean_object* v_x_3051_){
_start:
{
uint8_t v_res_3052_; lean_object* v_r_3053_; 
v_res_3052_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_a_3050_, v_x_3051_);
lean_dec(v_x_3051_);
lean_dec(v_a_3050_);
v_r_3053_ = lean_box(v_res_3052_);
return v_r_3053_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_3057_ = lean_unsigned_to_nat(6u);
v___x_3058_ = lean_unsigned_to_nat(94u);
v___x_3059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3060_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3061_ = l_mkPanicMessageWithDecl(v___x_3060_, v___x_3059_, v___x_3058_, v___x_3057_, v___x_3056_);
return v___x_3061_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3));
v___x_3064_ = lean_unsigned_to_nat(6u);
v___x_3065_ = lean_unsigned_to_nat(91u);
v___x_3066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3067_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3068_ = l_mkPanicMessageWithDecl(v___x_3067_, v___x_3066_, v___x_3065_, v___x_3064_, v___x_3063_);
return v___x_3068_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5));
v___x_3071_ = lean_unsigned_to_nat(6u);
v___x_3072_ = lean_unsigned_to_nat(92u);
v___x_3073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3074_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3075_ = l_mkPanicMessageWithDecl(v___x_3074_, v___x_3073_, v___x_3072_, v___x_3071_, v___x_3070_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7));
v___x_3078_ = lean_unsigned_to_nat(6u);
v___x_3079_ = lean_unsigned_to_nat(93u);
v___x_3080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3081_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3082_ = l_mkPanicMessageWithDecl(v___x_3081_, v___x_3080_, v___x_3079_, v___x_3078_, v___x_3077_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(lean_object* v_a_3083_, lean_object* v_as_3084_, size_t v_sz_3085_, size_t v_i_3086_, lean_object* v_b_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_usize_dec_lt(v_i_3086_, v_sz_3085_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_b_3087_);
return v___x_3100_;
}
else
{
lean_object* v_snd_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3157_; 
v_snd_3101_ = lean_ctor_get(v_b_3087_, 1);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_b_3087_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v_b_3087_, 0);
lean_dec(v_unused_3158_);
v___x_3103_ = v_b_3087_;
v_isShared_3104_ = v_isSharedCheck_3157_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_snd_3101_);
lean_dec(v_b_3087_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3157_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v_a_3107_; lean_object* v___y_3118_; lean_object* v_a_3141_; 
v___x_3105_ = lean_box(0);
v_a_3141_ = lean_array_uget_borrowed(v_as_3084_, v_i_3086_);
if (lean_obj_tag(v_a_3141_) == 1)
{
lean_object* v_val_3142_; lean_object* v_p_3143_; uint8_t v___x_3144_; 
v_val_3142_ = lean_ctor_get(v_a_3141_, 0);
v_p_3143_ = lean_ctor_get(v_val_3142_, 0);
v___x_3144_ = l_Int_Linear_Poly_isSorted(v_p_3143_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3146_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3145_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
v___y_3118_ = v___x_3146_;
goto v___jp_3117_;
}
else
{
uint8_t v___x_3147_; 
v___x_3147_ = l_Int_Linear_Poly_checkCoeffs(v_p_3143_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3149_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3148_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
v___y_3118_ = v___x_3149_;
goto v___jp_3117_;
}
else
{
lean_object* v_elimStack_3150_; uint8_t v___x_3151_; 
v_elimStack_3150_ = lean_ctor_get(v_a_3083_, 11);
v___x_3151_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3101_, v_elimStack_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3153_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3152_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
v___y_3118_ = v___x_3153_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3154_ = l_Int_Linear_Poly_coeff(v_p_3143_, v_snd_3101_);
v___x_3155_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_3156_ = lean_int_dec_eq(v___x_3154_, v___x_3155_);
lean_dec(v___x_3154_);
if (v___x_3156_ == 0)
{
if (v___x_3151_ == 0)
{
goto v___jp_3138_;
}
else
{
goto v___jp_3114_;
}
}
else
{
goto v___jp_3138_;
}
}
}
}
}
else
{
goto v___jp_3114_;
}
v___jp_3106_:
{
lean_object* v___x_3109_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 1, v_a_3107_);
lean_ctor_set(v___x_3103_, 0, v___x_3105_);
v___x_3109_ = v___x_3103_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_a_3107_);
v___x_3109_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
size_t v___x_3110_; size_t v___x_3111_; 
v___x_3110_ = ((size_t)1ULL);
v___x_3111_ = lean_usize_add(v_i_3086_, v___x_3110_);
v_i_3086_ = v___x_3111_;
v_b_3087_ = v___x_3109_;
goto _start;
}
}
v___jp_3114_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_nat_add(v_snd_3101_, v___x_3115_);
lean_dec(v_snd_3101_);
v_a_3107_ = v___x_3116_;
goto v___jp_3106_;
}
v___jp_3117_:
{
if (lean_obj_tag(v___y_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3129_; 
v_a_3119_ = lean_ctor_get(v___y_3118_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___y_3118_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3121_ = v___y_3118_;
v_isShared_3122_ = v_isSharedCheck_3129_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___y_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3129_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
if (lean_obj_tag(v_a_3119_) == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
lean_del_object(v___x_3103_);
v___x_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3123_, 0, v_a_3119_);
v___x_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
lean_ctor_set(v___x_3124_, 1, v_snd_3101_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3124_);
v___x_3126_ = v___x_3121_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
else
{
lean_object* v_a_3128_; 
lean_del_object(v___x_3121_);
lean_dec(v_snd_3101_);
v_a_3128_ = lean_ctor_get(v_a_3119_, 0);
lean_inc(v_a_3128_);
lean_dec_ref(v_a_3119_);
v_a_3107_ = v_a_3128_;
goto v___jp_3106_;
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_del_object(v___x_3103_);
lean_dec(v_snd_3101_);
v_a_3130_ = lean_ctor_get(v___y_3118_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___y_3118_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___y_3118_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___y_3118_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
v___jp_3138_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3140_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3139_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
v___y_3118_ = v___x_3140_;
goto v___jp_3117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_a_3159_, lean_object* v_as_3160_, lean_object* v_sz_3161_, lean_object* v_i_3162_, lean_object* v_b_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
size_t v_sz_boxed_3175_; size_t v_i_boxed_3176_; lean_object* v_res_3177_; 
v_sz_boxed_3175_ = lean_unbox_usize(v_sz_3161_);
lean_dec(v_sz_3161_);
v_i_boxed_3176_ = lean_unbox_usize(v_i_3162_);
lean_dec(v_i_3162_);
v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3159_, v_as_3160_, v_sz_boxed_3175_, v_i_boxed_3176_, v_b_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v_as_3160_);
lean_dec_ref(v_a_3159_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(lean_object* v_a_3178_, lean_object* v_as_3179_, size_t v_sz_3180_, size_t v_i_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
uint8_t v___x_3194_; 
v___x_3194_ = lean_usize_dec_lt(v_i_3181_, v_sz_3180_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v_b_3182_);
return v___x_3195_;
}
else
{
lean_object* v_snd_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3252_; 
v_snd_3196_ = lean_ctor_get(v_b_3182_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_b_3182_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v_b_3182_, 0);
lean_dec(v_unused_3253_);
v___x_3198_ = v_b_3182_;
v_isShared_3199_ = v_isSharedCheck_3252_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_snd_3196_);
lean_dec(v_b_3182_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3252_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v_a_3202_; lean_object* v___y_3213_; lean_object* v_a_3236_; 
v___x_3200_ = lean_box(0);
v_a_3236_ = lean_array_uget_borrowed(v_as_3179_, v_i_3181_);
if (lean_obj_tag(v_a_3236_) == 1)
{
lean_object* v_val_3237_; lean_object* v_p_3238_; uint8_t v___x_3239_; 
v_val_3237_ = lean_ctor_get(v_a_3236_, 0);
v_p_3238_ = lean_ctor_get(v_val_3237_, 0);
v___x_3239_ = l_Int_Linear_Poly_isSorted(v_p_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3241_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3240_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
v___y_3213_ = v___x_3241_;
goto v___jp_3212_;
}
else
{
uint8_t v___x_3242_; 
v___x_3242_ = l_Int_Linear_Poly_checkCoeffs(v_p_3238_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3244_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3243_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
v___y_3213_ = v___x_3244_;
goto v___jp_3212_;
}
else
{
lean_object* v_elimStack_3245_; uint8_t v___x_3246_; 
v_elimStack_3245_ = lean_ctor_get(v_a_3178_, 11);
v___x_3246_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3196_, v_elimStack_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3248_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3247_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
v___y_3213_ = v___x_3248_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3249_ = l_Int_Linear_Poly_coeff(v_p_3238_, v_snd_3196_);
v___x_3250_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_3251_ = lean_int_dec_eq(v___x_3249_, v___x_3250_);
lean_dec(v___x_3249_);
if (v___x_3251_ == 0)
{
if (v___x_3246_ == 0)
{
goto v___jp_3233_;
}
else
{
goto v___jp_3209_;
}
}
else
{
goto v___jp_3233_;
}
}
}
}
}
else
{
goto v___jp_3209_;
}
v___jp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 1, v_a_3202_);
lean_ctor_set(v___x_3198_, 0, v___x_3200_);
v___x_3204_ = v___x_3198_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_a_3202_);
v___x_3204_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
size_t v___x_3205_; size_t v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = ((size_t)1ULL);
v___x_3206_ = lean_usize_add(v_i_3181_, v___x_3205_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3178_, v_as_3179_, v_sz_3180_, v___x_3206_, v___x_3204_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
return v___x_3207_;
}
}
v___jp_3209_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_unsigned_to_nat(1u);
v___x_3211_ = lean_nat_add(v_snd_3196_, v___x_3210_);
lean_dec(v_snd_3196_);
v_a_3202_ = v___x_3211_;
goto v___jp_3201_;
}
v___jp_3212_:
{
if (lean_obj_tag(v___y_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3224_; 
v_a_3214_ = lean_ctor_get(v___y_3213_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___y_3213_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3216_ = v___y_3213_;
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___y_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
if (lean_obj_tag(v_a_3214_) == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_del_object(v___x_3198_);
v___x_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_a_3214_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
lean_ctor_set(v___x_3219_, 1, v_snd_3196_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3219_);
v___x_3221_ = v___x_3216_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
else
{
lean_object* v_a_3223_; 
lean_del_object(v___x_3216_);
lean_dec(v_snd_3196_);
v_a_3223_ = lean_ctor_get(v_a_3214_, 0);
lean_inc(v_a_3223_);
lean_dec_ref(v_a_3214_);
v_a_3202_ = v_a_3223_;
goto v___jp_3201_;
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_del_object(v___x_3198_);
lean_dec(v_snd_3196_);
v_a_3225_ = lean_ctor_get(v___y_3213_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___y_3213_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___y_3213_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___y_3213_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
v___jp_3233_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3235_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3234_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
v___y_3213_ = v___x_3235_;
goto v___jp_3212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3___boxed(lean_object* v_a_3254_, lean_object* v_as_3255_, lean_object* v_sz_3256_, lean_object* v_i_3257_, lean_object* v_b_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
size_t v_sz_boxed_3270_; size_t v_i_boxed_3271_; lean_object* v_res_3272_; 
v_sz_boxed_3270_ = lean_unbox_usize(v_sz_3256_);
lean_dec(v_sz_3256_);
v_i_boxed_3271_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3254_, v_as_3255_, v_sz_boxed_3270_, v_i_boxed_3271_, v_b_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v_as_3255_);
lean_dec_ref(v_a_3254_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(lean_object* v_init_3273_, lean_object* v_a_3274_, lean_object* v_n_3275_, lean_object* v_b_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
if (lean_obj_tag(v_n_3275_) == 0)
{
lean_object* v_cs_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; size_t v_sz_3291_; size_t v___x_3292_; lean_object* v___x_3293_; 
v_cs_3288_ = lean_ctor_get(v_n_3275_, 0);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_ctor_set(v___x_3290_, 1, v_b_3276_);
v_sz_3291_ = lean_array_size(v_cs_3288_);
v___x_3292_ = ((size_t)0ULL);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3273_, v_a_3274_, v_cs_3288_, v_sz_3291_, v___x_3292_, v___x_3290_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3308_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3296_ = v___x_3293_;
v_isShared_3297_ = v_isSharedCheck_3308_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3293_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3308_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v_fst_3298_; 
v_fst_3298_ = lean_ctor_get(v_a_3294_, 0);
if (lean_obj_tag(v_fst_3298_) == 0)
{
lean_object* v_snd_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v_snd_3299_ = lean_ctor_get(v_a_3294_, 1);
lean_inc(v_snd_3299_);
lean_dec(v_a_3294_);
v___x_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3300_, 0, v_snd_3299_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v___x_3300_);
v___x_3302_ = v___x_3296_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
else
{
lean_object* v_val_3304_; lean_object* v___x_3306_; 
lean_inc_ref(v_fst_3298_);
lean_dec(v_a_3294_);
v_val_3304_ = lean_ctor_get(v_fst_3298_, 0);
lean_inc(v_val_3304_);
lean_dec_ref(v_fst_3298_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v_val_3304_);
v___x_3306_ = v___x_3296_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_val_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
v_a_3309_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3293_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3293_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
else
{
lean_object* v_vs_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; size_t v_sz_3320_; size_t v___x_3321_; lean_object* v___x_3322_; 
v_vs_3317_ = lean_ctor_get(v_n_3275_, 0);
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
lean_ctor_set(v___x_3319_, 1, v_b_3276_);
v_sz_3320_ = lean_array_size(v_vs_3317_);
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3274_, v_vs_3317_, v_sz_3320_, v___x_3321_, v___x_3319_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3337_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3337_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3337_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v_fst_3327_; 
v_fst_3327_ = lean_ctor_get(v_a_3323_, 0);
if (lean_obj_tag(v_fst_3327_) == 0)
{
lean_object* v_snd_3328_; lean_object* v___x_3329_; lean_object* v___x_3331_; 
v_snd_3328_ = lean_ctor_get(v_a_3323_, 1);
lean_inc(v_snd_3328_);
lean_dec(v_a_3323_);
v___x_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3329_, 0, v_snd_3328_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v___x_3329_);
v___x_3331_ = v___x_3325_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
else
{
lean_object* v_val_3333_; lean_object* v___x_3335_; 
lean_inc_ref(v_fst_3327_);
lean_dec(v_a_3323_);
v_val_3333_ = lean_ctor_get(v_fst_3327_, 0);
lean_inc(v_val_3333_);
lean_dec_ref(v_fst_3327_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v_val_3333_);
v___x_3335_ = v___x_3325_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_val_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
v_a_3338_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3322_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3322_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(lean_object* v_init_3346_, lean_object* v_a_3347_, lean_object* v_as_3348_, size_t v_sz_3349_, size_t v_i_3350_, lean_object* v_b_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_usize_dec_lt(v_i_3350_, v_sz_3349_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_b_3351_);
return v___x_3364_;
}
else
{
lean_object* v_snd_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3399_; 
v_snd_3365_ = lean_ctor_get(v_b_3351_, 1);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_b_3351_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; 
v_unused_3400_ = lean_ctor_get(v_b_3351_, 0);
lean_dec(v_unused_3400_);
v___x_3367_ = v_b_3351_;
v_isShared_3368_ = v_isSharedCheck_3399_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_snd_3365_);
lean_dec(v_b_3351_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3399_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v_a_3369_; lean_object* v___x_3370_; 
v_a_3369_ = lean_array_uget_borrowed(v_as_3348_, v_i_3350_);
lean_inc(v_snd_3365_);
v___x_3370_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3346_, v_a_3347_, v_a_3369_, v_snd_3365_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3390_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3390_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3390_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
if (lean_obj_tag(v_a_3371_) == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_a_3371_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3375_);
v___x_3377_ = v___x_3367_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_snd_3365_);
v___x_3377_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3377_);
v___x_3379_ = v___x_3373_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
lean_del_object(v___x_3373_);
lean_dec(v_snd_3365_);
v_a_3382_ = lean_ctor_get(v_a_3371_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v_a_3371_);
v___x_3383_ = lean_box(0);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 1, v_a_3382_);
lean_ctor_set(v___x_3367_, 0, v___x_3383_);
v___x_3385_ = v___x_3367_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3382_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
size_t v___x_3386_; size_t v___x_3387_; 
v___x_3386_ = ((size_t)1ULL);
v___x_3387_ = lean_usize_add(v_i_3350_, v___x_3386_);
v_i_3350_ = v___x_3387_;
v_b_3351_ = v___x_3385_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_del_object(v___x_3367_);
lean_dec(v_snd_3365_);
v_a_3391_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3370_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3370_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_3401_ = _args[0];
lean_object* v_a_3402_ = _args[1];
lean_object* v_as_3403_ = _args[2];
lean_object* v_sz_3404_ = _args[3];
lean_object* v_i_3405_ = _args[4];
lean_object* v_b_3406_ = _args[5];
lean_object* v___y_3407_ = _args[6];
lean_object* v___y_3408_ = _args[7];
lean_object* v___y_3409_ = _args[8];
lean_object* v___y_3410_ = _args[9];
lean_object* v___y_3411_ = _args[10];
lean_object* v___y_3412_ = _args[11];
lean_object* v___y_3413_ = _args[12];
lean_object* v___y_3414_ = _args[13];
lean_object* v___y_3415_ = _args[14];
lean_object* v___y_3416_ = _args[15];
lean_object* v___y_3417_ = _args[16];
_start:
{
size_t v_sz_boxed_3418_; size_t v_i_boxed_3419_; lean_object* v_res_3420_; 
v_sz_boxed_3418_ = lean_unbox_usize(v_sz_3404_);
lean_dec(v_sz_3404_);
v_i_boxed_3419_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_res_3420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3401_, v_a_3402_, v_as_3403_, v_sz_boxed_3418_, v_i_boxed_3419_, v_b_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v_as_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_init_3401_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1___boxed(lean_object* v_init_3421_, lean_object* v_a_3422_, lean_object* v_n_3423_, lean_object* v_b_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3421_, v_a_3422_, v_n_3423_, v_b_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v_n_3423_);
lean_dec_ref(v_a_3422_);
lean_dec(v_init_3421_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(lean_object* v_a_3437_, lean_object* v_as_3438_, size_t v_sz_3439_, size_t v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_usize_dec_lt(v_i_3440_, v_sz_3439_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3454_, 0, v_b_3441_);
return v___x_3454_;
}
else
{
lean_object* v_snd_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3518_; 
v_snd_3455_ = lean_ctor_get(v_b_3441_, 1);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_b_3441_);
if (v_isSharedCheck_3518_ == 0)
{
lean_object* v_unused_3519_; 
v_unused_3519_ = lean_ctor_get(v_b_3441_, 0);
lean_dec(v_unused_3519_);
v___x_3457_ = v_b_3441_;
v_isShared_3458_ = v_isSharedCheck_3518_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_snd_3455_);
lean_dec(v_b_3441_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3518_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v_a_3461_; lean_object* v___y_3472_; lean_object* v_a_3502_; 
v___x_3459_ = lean_box(0);
v_a_3502_ = lean_array_uget_borrowed(v_as_3438_, v_i_3440_);
if (lean_obj_tag(v_a_3502_) == 1)
{
lean_object* v_val_3503_; lean_object* v_p_3504_; uint8_t v___x_3505_; 
v_val_3503_ = lean_ctor_get(v_a_3502_, 0);
v_p_3504_ = lean_ctor_get(v_val_3503_, 0);
v___x_3505_ = l_Int_Linear_Poly_isSorted(v_p_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3507_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3506_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
v___y_3472_ = v___x_3507_;
goto v___jp_3471_;
}
else
{
uint8_t v___x_3508_; 
v___x_3508_ = l_Int_Linear_Poly_checkCoeffs(v_p_3504_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3510_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3509_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
v___y_3472_ = v___x_3510_;
goto v___jp_3471_;
}
else
{
lean_object* v_elimStack_3511_; uint8_t v___x_3512_; 
v_elimStack_3511_ = lean_ctor_get(v_a_3437_, 11);
v___x_3512_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3455_, v_elimStack_3511_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3514_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3513_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
v___y_3472_ = v___x_3514_;
goto v___jp_3471_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = l_Int_Linear_Poly_coeff(v_p_3504_, v_snd_3455_);
v___x_3516_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_3517_ = lean_int_dec_eq(v___x_3515_, v___x_3516_);
lean_dec(v___x_3515_);
if (v___x_3517_ == 0)
{
if (v___x_3512_ == 0)
{
goto v___jp_3499_;
}
else
{
goto v___jp_3468_;
}
}
else
{
goto v___jp_3499_;
}
}
}
}
}
else
{
goto v___jp_3468_;
}
v___jp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 1, v_a_3461_);
lean_ctor_set(v___x_3457_, 0, v___x_3459_);
v___x_3463_ = v___x_3457_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_a_3461_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
size_t v___x_3464_; size_t v___x_3465_; 
v___x_3464_ = ((size_t)1ULL);
v___x_3465_ = lean_usize_add(v_i_3440_, v___x_3464_);
v_i_3440_ = v___x_3465_;
v_b_3441_ = v___x_3463_;
goto _start;
}
}
v___jp_3468_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_unsigned_to_nat(1u);
v___x_3470_ = lean_nat_add(v_snd_3455_, v___x_3469_);
lean_dec(v_snd_3455_);
v_a_3461_ = v___x_3470_;
goto v___jp_3460_;
}
v___jp_3471_:
{
if (lean_obj_tag(v___y_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3490_; 
v_a_3473_ = lean_ctor_get(v___y_3472_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___y_3472_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3475_ = v___y_3472_;
v_isShared_3476_ = v_isSharedCheck_3490_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___y_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3490_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
if (lean_obj_tag(v_a_3473_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3488_; 
lean_del_object(v___x_3457_);
v_a_3477_ = lean_ctor_get(v_a_3473_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_a_3473_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3479_ = v_a_3473_;
v_isShared_3480_ = v_isSharedCheck_3488_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v_a_3473_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3488_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 1);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
lean_ctor_set(v___x_3483_, 1, v_snd_3455_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3483_);
v___x_3485_ = v___x_3475_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_a_3489_; 
lean_del_object(v___x_3475_);
lean_dec(v_snd_3455_);
v_a_3489_ = lean_ctor_get(v_a_3473_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v_a_3473_);
v_a_3461_ = v_a_3489_;
goto v___jp_3460_;
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_del_object(v___x_3457_);
lean_dec(v_snd_3455_);
v_a_3491_ = lean_ctor_get(v___y_3472_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___y_3472_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___y_3472_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___y_3472_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
v___jp_3499_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3501_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3500_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
v___y_3472_ = v___x_3501_;
goto v___jp_3471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5___boxed(lean_object* v_a_3520_, lean_object* v_as_3521_, lean_object* v_sz_3522_, lean_object* v_i_3523_, lean_object* v_b_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
size_t v_sz_boxed_3536_; size_t v_i_boxed_3537_; lean_object* v_res_3538_; 
v_sz_boxed_3536_ = lean_unbox_usize(v_sz_3522_);
lean_dec(v_sz_3522_);
v_i_boxed_3537_ = lean_unbox_usize(v_i_3523_);
lean_dec(v_i_3523_);
v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3520_, v_as_3521_, v_sz_boxed_3536_, v_i_boxed_3537_, v_b_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v_as_3521_);
lean_dec_ref(v_a_3520_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(lean_object* v_a_3539_, lean_object* v_as_3540_, size_t v_sz_3541_, size_t v_i_3542_, lean_object* v_b_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
uint8_t v___x_3555_; 
v___x_3555_ = lean_usize_dec_lt(v_i_3542_, v_sz_3541_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_b_3543_);
return v___x_3556_;
}
else
{
lean_object* v_snd_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3620_; 
v_snd_3557_ = lean_ctor_get(v_b_3543_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_b_3543_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v_b_3543_, 0);
lean_dec(v_unused_3621_);
v___x_3559_ = v_b_3543_;
v_isShared_3560_ = v_isSharedCheck_3620_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_snd_3557_);
lean_dec(v_b_3543_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3620_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v_a_3563_; lean_object* v___y_3574_; lean_object* v_a_3604_; 
v___x_3561_ = lean_box(0);
v_a_3604_ = lean_array_uget_borrowed(v_as_3540_, v_i_3542_);
if (lean_obj_tag(v_a_3604_) == 1)
{
lean_object* v_val_3605_; lean_object* v_p_3606_; uint8_t v___x_3607_; 
v_val_3605_ = lean_ctor_get(v_a_3604_, 0);
v_p_3606_ = lean_ctor_get(v_val_3605_, 0);
v___x_3607_ = l_Int_Linear_Poly_isSorted(v_p_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3609_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3608_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
v___y_3574_ = v___x_3609_;
goto v___jp_3573_;
}
else
{
uint8_t v___x_3610_; 
v___x_3610_ = l_Int_Linear_Poly_checkCoeffs(v_p_3606_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3612_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3611_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
v___y_3574_ = v___x_3612_;
goto v___jp_3573_;
}
else
{
lean_object* v_elimStack_3613_; uint8_t v___x_3614_; 
v_elimStack_3613_ = lean_ctor_get(v_a_3539_, 11);
v___x_3614_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3557_, v_elimStack_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3616_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3615_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
v___y_3574_ = v___x_3616_;
goto v___jp_3573_;
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3617_ = l_Int_Linear_Poly_coeff(v_p_3606_, v_snd_3557_);
v___x_3618_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_3619_ = lean_int_dec_eq(v___x_3617_, v___x_3618_);
lean_dec(v___x_3617_);
if (v___x_3619_ == 0)
{
if (v___x_3614_ == 0)
{
goto v___jp_3601_;
}
else
{
goto v___jp_3570_;
}
}
else
{
goto v___jp_3601_;
}
}
}
}
}
else
{
goto v___jp_3570_;
}
v___jp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v_a_3563_);
lean_ctor_set(v___x_3559_, 0, v___x_3561_);
v___x_3565_ = v___x_3559_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_a_3563_);
v___x_3565_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
size_t v___x_3566_; size_t v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = ((size_t)1ULL);
v___x_3567_ = lean_usize_add(v_i_3542_, v___x_3566_);
v___x_3568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3539_, v_as_3540_, v_sz_3541_, v___x_3567_, v___x_3565_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
return v___x_3568_;
}
}
v___jp_3570_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_unsigned_to_nat(1u);
v___x_3572_ = lean_nat_add(v_snd_3557_, v___x_3571_);
lean_dec(v_snd_3557_);
v_a_3563_ = v___x_3572_;
goto v___jp_3562_;
}
v___jp_3573_:
{
if (lean_obj_tag(v___y_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3592_; 
v_a_3575_ = lean_ctor_get(v___y_3574_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___y_3574_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3577_ = v___y_3574_;
v_isShared_3578_ = v_isSharedCheck_3592_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___y_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3592_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
if (lean_obj_tag(v_a_3575_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3590_; 
lean_del_object(v___x_3559_);
v_a_3579_ = lean_ctor_get(v_a_3575_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_a_3575_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3581_ = v_a_3575_;
v_isShared_3582_ = v_isSharedCheck_3590_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v_a_3575_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3590_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 1);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3587_; 
v___x_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
lean_ctor_set(v___x_3585_, 1, v_snd_3557_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3585_);
v___x_3587_ = v___x_3577_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_object* v_a_3591_; 
lean_del_object(v___x_3577_);
lean_dec(v_snd_3557_);
v_a_3591_ = lean_ctor_get(v_a_3575_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v_a_3575_);
v_a_3563_ = v_a_3591_;
goto v___jp_3562_;
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_del_object(v___x_3559_);
lean_dec(v_snd_3557_);
v_a_3593_ = lean_ctor_get(v___y_3574_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___y_3574_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___y_3574_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___y_3574_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
v___jp_3601_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3603_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3602_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
v___y_3574_ = v___x_3603_;
goto v___jp_3573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2___boxed(lean_object* v_a_3622_, lean_object* v_as_3623_, lean_object* v_sz_3624_, lean_object* v_i_3625_, lean_object* v_b_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
size_t v_sz_boxed_3638_; size_t v_i_boxed_3639_; lean_object* v_res_3640_; 
v_sz_boxed_3638_ = lean_unbox_usize(v_sz_3624_);
lean_dec(v_sz_3624_);
v_i_boxed_3639_ = lean_unbox_usize(v_i_3625_);
lean_dec(v_i_3625_);
v_res_3640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3622_, v_as_3623_, v_sz_boxed_3638_, v_i_boxed_3639_, v_b_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v_as_3623_);
lean_dec_ref(v_a_3622_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(lean_object* v_a_3641_, lean_object* v_t_3642_, lean_object* v_init_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_root_3655_; lean_object* v_tail_3656_; lean_object* v___x_3657_; 
v_root_3655_ = lean_ctor_get(v_t_3642_, 0);
v_tail_3656_ = lean_ctor_get(v_t_3642_, 1);
lean_inc(v_init_3643_);
v___x_3657_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3643_, v_a_3641_, v_root_3655_, v_init_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec(v_init_3643_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3694_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3694_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3694_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
if (lean_obj_tag(v_a_3658_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; 
v_a_3662_ = lean_ctor_get(v_a_3658_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v_a_3658_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v_a_3662_);
v___x_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; size_t v_sz_3669_; size_t v___x_3670_; lean_object* v___x_3671_; 
lean_del_object(v___x_3660_);
v_a_3666_ = lean_ctor_get(v_a_3658_, 0);
lean_inc(v_a_3666_);
lean_dec_ref(v_a_3658_);
v___x_3667_ = lean_box(0);
v___x_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
lean_ctor_set(v___x_3668_, 1, v_a_3666_);
v_sz_3669_ = lean_array_size(v_tail_3656_);
v___x_3670_ = ((size_t)0ULL);
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3641_, v_tail_3656_, v_sz_3669_, v___x_3670_, v___x_3668_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3685_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3685_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3685_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v_fst_3676_; 
v_fst_3676_ = lean_ctor_get(v_a_3672_, 0);
if (lean_obj_tag(v_fst_3676_) == 0)
{
lean_object* v_snd_3677_; lean_object* v___x_3679_; 
v_snd_3677_ = lean_ctor_get(v_a_3672_, 1);
lean_inc(v_snd_3677_);
lean_dec(v_a_3672_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v_snd_3677_);
v___x_3679_ = v___x_3674_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_snd_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
else
{
lean_object* v_val_3681_; lean_object* v___x_3683_; 
lean_inc_ref(v_fst_3676_);
lean_dec(v_a_3672_);
v_val_3681_ = lean_ctor_get(v_fst_3676_, 0);
lean_inc(v_val_3681_);
lean_dec_ref(v_fst_3676_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v_val_3681_);
v___x_3683_ = v___x_3674_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_val_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
v_a_3686_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3671_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3671_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
v_a_3695_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3657_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3657_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1___boxed(lean_object* v_a_3703_, lean_object* v_t_3704_, lean_object* v_init_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3703_, v_t_3704_, v_init_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v_t_3704_);
lean_dec_ref(v_a_3703_);
return v_res_3717_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3719_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0));
v___x_3720_ = lean_unsigned_to_nat(2u);
v___x_3721_ = lean_unsigned_to_nat(87u);
v___x_3722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3723_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3724_ = l_mkPanicMessageWithDecl(v___x_3723_, v___x_3722_, v___x_3721_, v___x_3720_, v___x_3719_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3725_, v_a_3733_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v_elimEqs_3738_; lean_object* v_vars_3739_; lean_object* v_size_3740_; lean_object* v_size_3741_; uint8_t v___x_3742_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref(v___x_3736_);
v_elimEqs_3738_ = lean_ctor_get(v_a_3737_, 10);
lean_inc_ref(v_elimEqs_3738_);
v_vars_3739_ = lean_ctor_get(v_a_3737_, 0);
v_size_3740_ = lean_ctor_get(v_elimEqs_3738_, 2);
v_size_3741_ = lean_ctor_get(v_vars_3739_, 2);
v___x_3742_ = lean_nat_dec_eq(v_size_3740_, v_size_3741_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec_ref(v_elimEqs_3738_);
lean_dec(v_a_3737_);
v___x_3743_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1);
v___x_3744_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_3743_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
return v___x_3744_;
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = lean_unsigned_to_nat(0u);
v___x_3746_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3737_, v_elimEqs_3738_, v___x_3745_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
lean_dec_ref(v_elimEqs_3738_);
lean_dec(v_a_3737_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3754_; 
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; 
v_unused_3755_ = lean_ctor_get(v___x_3746_, 0);
lean_dec(v_unused_3755_);
v___x_3748_ = v___x_3746_;
v_isShared_3749_ = v_isSharedCheck_3754_;
goto v_resetjp_3747_;
}
else
{
lean_dec(v___x_3746_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3754_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3750_ = lean_box(0);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3750_);
v___x_3752_ = v___x_3748_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
v_a_3756_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3746_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3746_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
v_a_3764_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3736_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3736_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___boxed(lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec(v_a_3772_);
return v_res_3783_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3786_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1));
v___x_3787_ = lean_unsigned_to_nat(4u);
v___x_3788_ = lean_unsigned_to_nat(99u);
v___x_3789_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0));
v___x_3790_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3791_ = l_mkPanicMessageWithDecl(v___x_3790_, v___x_3789_, v___x_3788_, v___x_3787_, v___x_3786_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(lean_object* v_as_x27_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
if (lean_obj_tag(v_as_x27_3792_) == 0)
{
lean_object* v___x_3805_; 
v___x_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3805_, 0, v_b_3793_);
return v___x_3805_;
}
else
{
lean_object* v_head_3806_; lean_object* v_tail_3807_; lean_object* v___x_3808_; 
v_head_3806_ = lean_ctor_get(v_as_x27_3792_, 0);
v_tail_3807_ = lean_ctor_get(v_as_x27_3792_, 1);
v___x_3808_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_head_3806_, v___y_3794_, v___y_3802_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; uint8_t v___x_3810_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_a_3809_);
lean_dec_ref(v___x_3808_);
v___x_3810_ = lean_unbox(v_a_3809_);
lean_dec(v_a_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3811_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2);
v___x_3812_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_3811_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3823_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3815_ = v___x_3812_;
v_isShared_3816_ = v_isSharedCheck_3823_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3812_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3823_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
if (lean_obj_tag(v_a_3813_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; 
v_a_3817_ = lean_ctor_get(v_a_3813_, 0);
lean_inc(v_a_3817_);
lean_dec_ref(v_a_3813_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v_a_3817_);
v___x_3819_ = v___x_3815_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3817_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
else
{
lean_object* v_a_3821_; 
lean_del_object(v___x_3815_);
v_a_3821_ = lean_ctor_get(v_a_3813_, 0);
lean_inc(v_a_3821_);
lean_dec_ref(v_a_3813_);
v_as_x27_3792_ = v_tail_3807_;
v_b_3793_ = v_a_3821_;
goto _start;
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
v_a_3824_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3812_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3812_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_box(0);
v_as_x27_3792_ = v_tail_3807_;
v_b_3793_ = v___x_3832_;
goto _start;
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
v_a_3834_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3808_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3808_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___boxed(lean_object* v_as_x27_3842_, lean_object* v_b_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3842_, v_b_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec(v_as_x27_3842_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3856_, v_a_3864_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v_elimStack_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref(v___x_3867_);
v_elimStack_3869_ = lean_ctor_get(v_a_3868_, 11);
lean_inc(v_elimStack_3869_);
lean_dec(v_a_3868_);
v___x_3870_ = lean_box(0);
v___x_3871_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_elimStack_3869_, v___x_3870_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_elimStack_3869_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3878_ == 0)
{
lean_object* v_unused_3879_; 
v_unused_3879_ = lean_ctor_get(v___x_3871_, 0);
lean_dec(v_unused_3879_);
v___x_3873_ = v___x_3871_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_dec(v___x_3871_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 0, v___x_3870_);
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3870_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
else
{
return v___x_3871_;
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_a_3880_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3867_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3867_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack___boxed(lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
lean_dec(v_a_3889_);
lean_dec(v_a_3888_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(lean_object* v_as_3900_, lean_object* v_as_x27_3901_, lean_object* v_b_3902_, lean_object* v_a_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3901_, v_b_3902_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___boxed(lean_object* v_as_3916_, lean_object* v_as_x27_3917_, lean_object* v_b_3918_, lean_object* v_a_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(v_as_3916_, v_as_x27_3917_, v_b_3918_, v_a_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec(v_as_x27_3917_);
lean_dec(v_as_3916_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_3935_, lean_object* v_as_3936_, size_t v_sz_3937_, size_t v_i_3938_, lean_object* v_b_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
uint8_t v___x_3951_; 
v___x_3951_ = lean_usize_dec_lt(v_i_3938_, v_sz_3937_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v_b_3939_);
return v___x_3952_;
}
else
{
lean_object* v_a_3953_; lean_object* v_p_3954_; lean_object* v___x_3955_; 
lean_dec_ref(v_b_3939_);
v_a_3953_ = lean_array_uget_borrowed(v_as_3936_, v_i_3938_);
v_p_3954_ = lean_ctor_get(v_a_3953_, 0);
v___x_3955_ = l_Int_Linear_Poly_checkCnstrOf(v_p_3954_, v_____s_3935_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v___x_3956_; size_t v___x_3957_; size_t v___x_3958_; 
lean_dec_ref(v___x_3955_);
v___x_3956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_3957_ = ((size_t)1ULL);
v___x_3958_ = lean_usize_add(v_i_3938_, v___x_3957_);
v_i_3938_ = v___x_3958_;
v_b_3939_ = v___x_3956_;
goto _start;
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
v_a_3960_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3955_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3955_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object* v_____s_3968_, lean_object* v_as_3969_, lean_object* v_sz_3970_, lean_object* v_i_3971_, lean_object* v_b_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
size_t v_sz_boxed_3984_; size_t v_i_boxed_3985_; lean_object* v_res_3986_; 
v_sz_boxed_3984_ = lean_unbox_usize(v_sz_3970_);
lean_dec(v_sz_3970_);
v_i_boxed_3985_ = lean_unbox_usize(v_i_3971_);
lean_dec(v_i_3971_);
v_res_3986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3968_, v_as_3969_, v_sz_boxed_3984_, v_i_boxed_3985_, v_b_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v_as_3969_);
lean_dec(v_____s_3968_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_3987_, lean_object* v_as_3988_, size_t v_sz_3989_, size_t v_i_3990_, lean_object* v_b_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
uint8_t v___x_4003_; 
v___x_4003_ = lean_usize_dec_lt(v_i_3990_, v_sz_3989_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v_b_3991_);
return v___x_4004_;
}
else
{
lean_object* v_a_4005_; lean_object* v_p_4006_; lean_object* v___x_4007_; 
lean_dec_ref(v_b_3991_);
v_a_4005_ = lean_array_uget_borrowed(v_as_3988_, v_i_3990_);
v_p_4006_ = lean_ctor_get(v_a_4005_, 0);
v___x_4007_ = l_Int_Linear_Poly_checkCnstrOf(v_p_4006_, v_____s_3987_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v___x_4008_; size_t v___x_4009_; size_t v___x_4010_; lean_object* v___x_4011_; 
lean_dec_ref(v___x_4007_);
v___x_4008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_4009_ = ((size_t)1ULL);
v___x_4010_ = lean_usize_add(v_i_3990_, v___x_4009_);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3987_, v_as_3988_, v_sz_3989_, v___x_4010_, v___x_4008_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
return v___x_4011_;
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4007_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4007_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object* v_____s_4020_, lean_object* v_as_4021_, lean_object* v_sz_4022_, lean_object* v_i_4023_, lean_object* v_b_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
size_t v_sz_boxed_4036_; size_t v_i_boxed_4037_; lean_object* v_res_4038_; 
v_sz_boxed_4036_ = lean_unbox_usize(v_sz_4022_);
lean_dec(v_sz_4022_);
v_i_boxed_4037_ = lean_unbox_usize(v_i_4023_);
lean_dec(v_i_4023_);
v_res_4038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4020_, v_as_4021_, v_sz_boxed_4036_, v_i_boxed_4037_, v_b_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v_as_4021_);
lean_dec(v_____s_4020_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_4042_, lean_object* v_as_4043_, size_t v_sz_4044_, size_t v_i_4045_, lean_object* v_b_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
uint8_t v___x_4058_; 
v___x_4058_ = lean_usize_dec_lt(v_i_4045_, v_sz_4044_);
if (v___x_4058_ == 0)
{
lean_object* v___x_4059_; 
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v_b_4046_);
return v___x_4059_;
}
else
{
lean_object* v_a_4060_; lean_object* v_p_4061_; lean_object* v___x_4062_; 
lean_dec_ref(v_b_4046_);
v_a_4060_ = lean_array_uget_borrowed(v_as_4043_, v_i_4045_);
v_p_4061_ = lean_ctor_get(v_a_4060_, 0);
v___x_4062_ = l_Int_Linear_Poly_checkCnstrOf(v_p_4061_, v_____s_4042_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v___x_4063_; size_t v___x_4064_; size_t v___x_4065_; 
lean_dec_ref(v___x_4062_);
v___x_4063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4064_ = ((size_t)1ULL);
v___x_4065_ = lean_usize_add(v_i_4045_, v___x_4064_);
v_i_4045_ = v___x_4065_;
v_b_4046_ = v___x_4063_;
goto _start;
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
v_a_4067_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4062_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4062_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_____s_4075_, lean_object* v_as_4076_, lean_object* v_sz_4077_, lean_object* v_i_4078_, lean_object* v_b_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
size_t v_sz_boxed_4091_; size_t v_i_boxed_4092_; lean_object* v_res_4093_; 
v_sz_boxed_4091_ = lean_unbox_usize(v_sz_4077_);
lean_dec(v_sz_4077_);
v_i_boxed_4092_ = lean_unbox_usize(v_i_4078_);
lean_dec(v_i_4078_);
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4075_, v_as_4076_, v_sz_boxed_4091_, v_i_boxed_4092_, v_b_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v_as_4076_);
lean_dec(v_____s_4075_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_4094_, lean_object* v_as_4095_, size_t v_sz_4096_, size_t v_i_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
uint8_t v___x_4110_; 
v___x_4110_ = lean_usize_dec_lt(v_i_4097_, v_sz_4096_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v_b_4098_);
return v___x_4111_;
}
else
{
lean_object* v_a_4112_; lean_object* v_p_4113_; lean_object* v___x_4114_; 
lean_dec_ref(v_b_4098_);
v_a_4112_ = lean_array_uget_borrowed(v_as_4095_, v_i_4097_);
v_p_4113_ = lean_ctor_get(v_a_4112_, 0);
v___x_4114_ = l_Int_Linear_Poly_checkCnstrOf(v_p_4113_, v_____s_4094_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v___x_4115_; size_t v___x_4116_; size_t v___x_4117_; lean_object* v___x_4118_; 
lean_dec_ref(v___x_4114_);
v___x_4115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4116_ = ((size_t)1ULL);
v___x_4117_ = lean_usize_add(v_i_4097_, v___x_4116_);
v___x_4118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4094_, v_as_4095_, v_sz_4096_, v___x_4117_, v___x_4115_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
return v___x_4118_;
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
v_a_4119_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4114_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4114_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_____s_4127_, lean_object* v_as_4128_, lean_object* v_sz_4129_, lean_object* v_i_4130_, lean_object* v_b_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
size_t v_sz_boxed_4143_; size_t v_i_boxed_4144_; lean_object* v_res_4145_; 
v_sz_boxed_4143_ = lean_unbox_usize(v_sz_4129_);
lean_dec(v_sz_4129_);
v_i_boxed_4144_ = lean_unbox_usize(v_i_4130_);
lean_dec(v_i_4130_);
v_res_4145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4127_, v_as_4128_, v_sz_boxed_4143_, v_i_boxed_4144_, v_b_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v_as_4128_);
lean_dec(v_____s_4127_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_init_4146_, lean_object* v_____s_4147_, lean_object* v_n_4148_, lean_object* v_b_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
if (lean_obj_tag(v_n_4148_) == 0)
{
lean_object* v_cs_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; size_t v_sz_4164_; size_t v___x_4165_; lean_object* v___x_4166_; 
v_cs_4161_ = lean_ctor_get(v_n_4148_, 0);
v___x_4162_ = lean_box(0);
v___x_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
lean_ctor_set(v___x_4163_, 1, v_b_4149_);
v_sz_4164_ = lean_array_size(v_cs_4161_);
v___x_4165_ = ((size_t)0ULL);
v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4146_, v_____s_4147_, v_cs_4161_, v_sz_4164_, v___x_4165_, v___x_4163_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4181_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4169_ = v___x_4166_;
v_isShared_4170_ = v_isSharedCheck_4181_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4181_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v_fst_4171_; 
v_fst_4171_ = lean_ctor_get(v_a_4167_, 0);
if (lean_obj_tag(v_fst_4171_) == 0)
{
lean_object* v_snd_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v_snd_4172_ = lean_ctor_get(v_a_4167_, 1);
lean_inc(v_snd_4172_);
lean_dec(v_a_4167_);
v___x_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4173_, 0, v_snd_4172_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4173_);
v___x_4175_ = v___x_4169_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
else
{
lean_object* v_val_4177_; lean_object* v___x_4179_; 
lean_inc_ref(v_fst_4171_);
lean_dec(v_a_4167_);
v_val_4177_ = lean_ctor_get(v_fst_4171_, 0);
lean_inc(v_val_4177_);
lean_dec_ref(v_fst_4171_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v_val_4177_);
v___x_4179_ = v___x_4169_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_val_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
v_a_4182_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4166_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4166_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
lean_object* v_vs_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; size_t v_sz_4193_; size_t v___x_4194_; lean_object* v___x_4195_; 
v_vs_4190_ = lean_ctor_get(v_n_4148_, 0);
v___x_4191_ = lean_box(0);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v_b_4149_);
v_sz_4193_ = lean_array_size(v_vs_4190_);
v___x_4194_ = ((size_t)0ULL);
v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4147_, v_vs_4190_, v_sz_4193_, v___x_4194_, v___x_4192_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4210_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4210_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4210_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v_fst_4200_; 
v_fst_4200_ = lean_ctor_get(v_a_4196_, 0);
if (lean_obj_tag(v_fst_4200_) == 0)
{
lean_object* v_snd_4201_; lean_object* v___x_4202_; lean_object* v___x_4204_; 
v_snd_4201_ = lean_ctor_get(v_a_4196_, 1);
lean_inc(v_snd_4201_);
lean_dec(v_a_4196_);
v___x_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4202_, 0, v_snd_4201_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4202_);
v___x_4204_ = v___x_4198_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4202_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
else
{
lean_object* v_val_4206_; lean_object* v___x_4208_; 
lean_inc_ref(v_fst_4200_);
lean_dec(v_a_4196_);
v_val_4206_ = lean_ctor_get(v_fst_4200_, 0);
lean_inc(v_val_4206_);
lean_dec_ref(v_fst_4200_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v_val_4206_);
v___x_4208_ = v___x_4198_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_val_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_a_4211_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4195_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4195_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_4219_, lean_object* v_____s_4220_, lean_object* v_as_4221_, size_t v_sz_4222_, size_t v_i_4223_, lean_object* v_b_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
uint8_t v___x_4236_; 
v___x_4236_ = lean_usize_dec_lt(v_i_4223_, v_sz_4222_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; 
v___x_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4237_, 0, v_b_4224_);
return v___x_4237_;
}
else
{
lean_object* v_snd_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4272_; 
v_snd_4238_ = lean_ctor_get(v_b_4224_, 1);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_b_4224_);
if (v_isSharedCheck_4272_ == 0)
{
lean_object* v_unused_4273_; 
v_unused_4273_ = lean_ctor_get(v_b_4224_, 0);
lean_dec(v_unused_4273_);
v___x_4240_ = v_b_4224_;
v_isShared_4241_ = v_isSharedCheck_4272_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_snd_4238_);
lean_dec(v_b_4224_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4272_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v_a_4242_; lean_object* v___x_4243_; 
v_a_4242_ = lean_array_uget_borrowed(v_as_4221_, v_i_4223_);
lean_inc(v_snd_4238_);
v___x_4243_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4219_, v_____s_4220_, v_a_4242_, v_snd_4238_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4263_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4246_ = v___x_4243_;
v_isShared_4247_ = v_isSharedCheck_4263_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4243_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4263_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
if (lean_obj_tag(v_a_4244_) == 0)
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4248_, 0, v_a_4244_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4248_);
v___x_4250_ = v___x_4240_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_snd_4238_);
v___x_4250_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4252_; 
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4250_);
v___x_4252_ = v___x_4246_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4250_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
lean_del_object(v___x_4246_);
lean_dec(v_snd_4238_);
v_a_4255_ = lean_ctor_get(v_a_4244_, 0);
lean_inc(v_a_4255_);
lean_dec_ref(v_a_4244_);
v___x_4256_ = lean_box(0);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 1, v_a_4255_);
lean_ctor_set(v___x_4240_, 0, v___x_4256_);
v___x_4258_ = v___x_4240_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4256_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v_a_4255_);
v___x_4258_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
size_t v___x_4259_; size_t v___x_4260_; 
v___x_4259_ = ((size_t)1ULL);
v___x_4260_ = lean_usize_add(v_i_4223_, v___x_4259_);
v_i_4223_ = v___x_4260_;
v_b_4224_ = v___x_4258_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_del_object(v___x_4240_);
lean_dec(v_snd_4238_);
v_a_4264_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4243_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4243_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_4274_ = _args[0];
lean_object* v_____s_4275_ = _args[1];
lean_object* v_as_4276_ = _args[2];
lean_object* v_sz_4277_ = _args[3];
lean_object* v_i_4278_ = _args[4];
lean_object* v_b_4279_ = _args[5];
lean_object* v___y_4280_ = _args[6];
lean_object* v___y_4281_ = _args[7];
lean_object* v___y_4282_ = _args[8];
lean_object* v___y_4283_ = _args[9];
lean_object* v___y_4284_ = _args[10];
lean_object* v___y_4285_ = _args[11];
lean_object* v___y_4286_ = _args[12];
lean_object* v___y_4287_ = _args[13];
lean_object* v___y_4288_ = _args[14];
lean_object* v___y_4289_ = _args[15];
lean_object* v___y_4290_ = _args[16];
_start:
{
size_t v_sz_boxed_4291_; size_t v_i_boxed_4292_; lean_object* v_res_4293_; 
v_sz_boxed_4291_ = lean_unbox_usize(v_sz_4277_);
lean_dec(v_sz_4277_);
v_i_boxed_4292_ = lean_unbox_usize(v_i_4278_);
lean_dec(v_i_4278_);
v_res_4293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4274_, v_____s_4275_, v_as_4276_, v_sz_boxed_4291_, v_i_boxed_4292_, v_b_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v_as_4276_);
lean_dec(v_____s_4275_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_init_4294_, lean_object* v_____s_4295_, lean_object* v_n_4296_, lean_object* v_b_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4294_, v_____s_4295_, v_n_4296_, v_b_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v_n_4296_);
lean_dec(v_____s_4295_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(lean_object* v_____s_4310_, lean_object* v_t_4311_, lean_object* v_init_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v_root_4324_; lean_object* v_tail_4325_; lean_object* v___x_4326_; 
v_root_4324_ = lean_ctor_get(v_t_4311_, 0);
v_tail_4325_ = lean_ctor_get(v_t_4311_, 1);
v___x_4326_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4312_, v_____s_4310_, v_root_4324_, v_init_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4363_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4329_ = v___x_4326_;
v_isShared_4330_ = v_isSharedCheck_4363_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4326_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4363_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
if (lean_obj_tag(v_a_4327_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4333_; 
v_a_4331_ = lean_ctor_get(v_a_4327_, 0);
lean_inc(v_a_4331_);
lean_dec_ref(v_a_4327_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v_a_4331_);
v___x_4333_ = v___x_4329_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4331_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; size_t v_sz_4338_; size_t v___x_4339_; lean_object* v___x_4340_; 
lean_del_object(v___x_4329_);
v_a_4335_ = lean_ctor_get(v_a_4327_, 0);
lean_inc(v_a_4335_);
lean_dec_ref(v_a_4327_);
v___x_4336_ = lean_box(0);
v___x_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
lean_ctor_set(v___x_4337_, 1, v_a_4335_);
v_sz_4338_ = lean_array_size(v_tail_4325_);
v___x_4339_ = ((size_t)0ULL);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4310_, v_tail_4325_, v_sz_4338_, v___x_4339_, v___x_4337_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4354_; 
v_a_4341_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4343_ = v___x_4340_;
v_isShared_4344_ = v_isSharedCheck_4354_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4340_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4354_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v_fst_4345_; 
v_fst_4345_ = lean_ctor_get(v_a_4341_, 0);
if (lean_obj_tag(v_fst_4345_) == 0)
{
lean_object* v_snd_4346_; lean_object* v___x_4348_; 
v_snd_4346_ = lean_ctor_get(v_a_4341_, 1);
lean_inc(v_snd_4346_);
lean_dec(v_a_4341_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 0, v_snd_4346_);
v___x_4348_ = v___x_4343_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_snd_4346_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
else
{
lean_object* v_val_4350_; lean_object* v___x_4352_; 
lean_inc_ref(v_fst_4345_);
lean_dec(v_a_4341_);
v_val_4350_ = lean_ctor_get(v_fst_4345_, 0);
lean_inc(v_val_4350_);
lean_dec_ref(v_fst_4345_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 0, v_val_4350_);
v___x_4352_ = v___x_4343_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_val_4350_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
v_a_4355_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4340_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4340_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
v_a_4364_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4326_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4326_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_4372_, lean_object* v_t_4373_, lean_object* v_init_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_____s_4372_, v_t_4373_, v_init_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v_t_4373_);
lean_dec(v_____s_4372_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_4387_, size_t v_sz_4388_, size_t v_i_4389_, lean_object* v_b_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
uint8_t v___x_4402_; 
v___x_4402_ = lean_usize_dec_lt(v_i_4389_, v_sz_4388_);
if (v___x_4402_ == 0)
{
lean_object* v___x_4403_; 
v___x_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4403_, 0, v_b_4390_);
return v___x_4403_;
}
else
{
lean_object* v_snd_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4428_; 
v_snd_4404_ = lean_ctor_get(v_b_4390_, 1);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_b_4390_);
if (v_isSharedCheck_4428_ == 0)
{
lean_object* v_unused_4429_; 
v_unused_4429_ = lean_ctor_get(v_b_4390_, 0);
lean_dec(v_unused_4429_);
v___x_4406_ = v_b_4390_;
v_isShared_4407_ = v_isSharedCheck_4428_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_snd_4404_);
lean_dec(v_b_4390_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4428_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v_a_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v_a_4408_ = lean_array_uget_borrowed(v_as_4387_, v_i_4389_);
v___x_4409_ = lean_box(0);
v___x_4410_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4404_, v_a_4408_, v___x_4409_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4415_; 
lean_dec_ref(v___x_4410_);
v___x_4411_ = lean_box(0);
v___x_4412_ = lean_unsigned_to_nat(1u);
v___x_4413_ = lean_nat_add(v_snd_4404_, v___x_4412_);
lean_dec(v_snd_4404_);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 1, v___x_4413_);
lean_ctor_set(v___x_4406_, 0, v___x_4411_);
v___x_4415_ = v___x_4406_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
size_t v___x_4416_; size_t v___x_4417_; 
v___x_4416_ = ((size_t)1ULL);
v___x_4417_ = lean_usize_add(v_i_4389_, v___x_4416_);
v_i_4389_ = v___x_4417_;
v_b_4390_ = v___x_4415_;
goto _start;
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_del_object(v___x_4406_);
lean_dec(v_snd_4404_);
v_a_4420_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4410_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4410_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_4430_, lean_object* v_sz_4431_, lean_object* v_i_4432_, lean_object* v_b_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
size_t v_sz_boxed_4445_; size_t v_i_boxed_4446_; lean_object* v_res_4447_; 
v_sz_boxed_4445_ = lean_unbox_usize(v_sz_4431_);
lean_dec(v_sz_4431_);
v_i_boxed_4446_ = lean_unbox_usize(v_i_4432_);
lean_dec(v_i_4432_);
v_res_4447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4430_, v_sz_boxed_4445_, v_i_boxed_4446_, v_b_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v_as_4430_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_4448_, size_t v_sz_4449_, size_t v_i_4450_, lean_object* v_b_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
uint8_t v___x_4463_; 
v___x_4463_ = lean_usize_dec_lt(v_i_4450_, v_sz_4449_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; 
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v_b_4451_);
return v___x_4464_;
}
else
{
lean_object* v_snd_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4489_; 
v_snd_4465_ = lean_ctor_get(v_b_4451_, 1);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_b_4451_);
if (v_isSharedCheck_4489_ == 0)
{
lean_object* v_unused_4490_; 
v_unused_4490_ = lean_ctor_get(v_b_4451_, 0);
lean_dec(v_unused_4490_);
v___x_4467_ = v_b_4451_;
v_isShared_4468_ = v_isSharedCheck_4489_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_snd_4465_);
lean_dec(v_b_4451_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4489_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v_a_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v_a_4469_ = lean_array_uget_borrowed(v_as_4448_, v_i_4450_);
v___x_4470_ = lean_box(0);
v___x_4471_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4465_, v_a_4469_, v___x_4470_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4476_; 
lean_dec_ref(v___x_4471_);
v___x_4472_ = lean_box(0);
v___x_4473_ = lean_unsigned_to_nat(1u);
v___x_4474_ = lean_nat_add(v_snd_4465_, v___x_4473_);
lean_dec(v_snd_4465_);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 1, v___x_4474_);
lean_ctor_set(v___x_4467_, 0, v___x_4472_);
v___x_4476_ = v___x_4467_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4472_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
size_t v___x_4477_; size_t v___x_4478_; lean_object* v___x_4479_; 
v___x_4477_ = ((size_t)1ULL);
v___x_4478_ = lean_usize_add(v_i_4450_, v___x_4477_);
v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4448_, v_sz_4449_, v___x_4478_, v___x_4476_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
return v___x_4479_;
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_del_object(v___x_4467_);
lean_dec(v_snd_4465_);
v_a_4481_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4471_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4471_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_4491_, lean_object* v_sz_4492_, lean_object* v_i_4493_, lean_object* v_b_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
size_t v_sz_boxed_4506_; size_t v_i_boxed_4507_; lean_object* v_res_4508_; 
v_sz_boxed_4506_ = lean_unbox_usize(v_sz_4492_);
lean_dec(v_sz_4492_);
v_i_boxed_4507_ = lean_unbox_usize(v_i_4493_);
lean_dec(v_i_4493_);
v_res_4508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_4491_, v_sz_boxed_4506_, v_i_boxed_4507_, v_b_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v_as_4491_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_init_4509_, lean_object* v_n_4510_, lean_object* v_b_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
if (lean_obj_tag(v_n_4510_) == 0)
{
lean_object* v_cs_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; size_t v_sz_4526_; size_t v___x_4527_; lean_object* v___x_4528_; 
v_cs_4523_ = lean_ctor_get(v_n_4510_, 0);
v___x_4524_ = lean_box(0);
v___x_4525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
lean_ctor_set(v___x_4525_, 1, v_b_4511_);
v_sz_4526_ = lean_array_size(v_cs_4523_);
v___x_4527_ = ((size_t)0ULL);
v___x_4528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4509_, v_cs_4523_, v_sz_4526_, v___x_4527_, v___x_4525_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4543_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4531_ = v___x_4528_;
v_isShared_4532_ = v_isSharedCheck_4543_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4528_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4543_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v_fst_4533_; 
v_fst_4533_ = lean_ctor_get(v_a_4529_, 0);
if (lean_obj_tag(v_fst_4533_) == 0)
{
lean_object* v_snd_4534_; lean_object* v___x_4535_; lean_object* v___x_4537_; 
v_snd_4534_ = lean_ctor_get(v_a_4529_, 1);
lean_inc(v_snd_4534_);
lean_dec(v_a_4529_);
v___x_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4535_, 0, v_snd_4534_);
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 0, v___x_4535_);
v___x_4537_ = v___x_4531_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4535_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
else
{
lean_object* v_val_4539_; lean_object* v___x_4541_; 
lean_inc_ref(v_fst_4533_);
lean_dec(v_a_4529_);
v_val_4539_ = lean_ctor_get(v_fst_4533_, 0);
lean_inc(v_val_4539_);
lean_dec_ref(v_fst_4533_);
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 0, v_val_4539_);
v___x_4541_ = v___x_4531_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_val_4539_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
v_a_4544_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4528_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4528_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
else
{
lean_object* v_vs_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; size_t v_sz_4555_; size_t v___x_4556_; lean_object* v___x_4557_; 
v_vs_4552_ = lean_ctor_get(v_n_4510_, 0);
v___x_4553_ = lean_box(0);
v___x_4554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
lean_ctor_set(v___x_4554_, 1, v_b_4511_);
v_sz_4555_ = lean_array_size(v_vs_4552_);
v___x_4556_ = ((size_t)0ULL);
v___x_4557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_4552_, v_sz_4555_, v___x_4556_, v___x_4554_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4572_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4560_ = v___x_4557_;
v_isShared_4561_ = v_isSharedCheck_4572_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4557_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4572_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v_fst_4562_; 
v_fst_4562_ = lean_ctor_get(v_a_4558_, 0);
if (lean_obj_tag(v_fst_4562_) == 0)
{
lean_object* v_snd_4563_; lean_object* v___x_4564_; lean_object* v___x_4566_; 
v_snd_4563_ = lean_ctor_get(v_a_4558_, 1);
lean_inc(v_snd_4563_);
lean_dec(v_a_4558_);
v___x_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4564_, 0, v_snd_4563_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v___x_4564_);
v___x_4566_ = v___x_4560_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4564_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
else
{
lean_object* v_val_4568_; lean_object* v___x_4570_; 
lean_inc_ref(v_fst_4562_);
lean_dec(v_a_4558_);
v_val_4568_ = lean_ctor_get(v_fst_4562_, 0);
lean_inc(v_val_4568_);
lean_dec_ref(v_fst_4562_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v_val_4568_);
v___x_4570_ = v___x_4560_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_val_4568_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
v_a_4573_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4557_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4557_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_init_4581_, lean_object* v_as_4582_, size_t v_sz_4583_, size_t v_i_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
uint8_t v___x_4597_; 
v___x_4597_ = lean_usize_dec_lt(v_i_4584_, v_sz_4583_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_b_4585_);
return v___x_4598_;
}
else
{
lean_object* v_snd_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4633_; 
v_snd_4599_ = lean_ctor_get(v_b_4585_, 1);
v_isSharedCheck_4633_ = !lean_is_exclusive(v_b_4585_);
if (v_isSharedCheck_4633_ == 0)
{
lean_object* v_unused_4634_; 
v_unused_4634_ = lean_ctor_get(v_b_4585_, 0);
lean_dec(v_unused_4634_);
v___x_4601_ = v_b_4585_;
v_isShared_4602_ = v_isSharedCheck_4633_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_snd_4599_);
lean_dec(v_b_4585_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4633_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v_a_4603_; lean_object* v___x_4604_; 
v_a_4603_ = lean_array_uget_borrowed(v_as_4582_, v_i_4584_);
lean_inc(v_snd_4599_);
v___x_4604_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4581_, v_a_4603_, v_snd_4599_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4624_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4624_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4624_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
if (lean_obj_tag(v_a_4605_) == 0)
{
lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4609_, 0, v_a_4605_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4609_);
v___x_4611_ = v___x_4601_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4615_, 1, v_snd_4599_);
v___x_4611_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4613_; 
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4611_);
v___x_4613_ = v___x_4607_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4611_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
else
{
lean_object* v_a_4616_; lean_object* v___x_4617_; lean_object* v___x_4619_; 
lean_del_object(v___x_4607_);
lean_dec(v_snd_4599_);
v_a_4616_ = lean_ctor_get(v_a_4605_, 0);
lean_inc(v_a_4616_);
lean_dec_ref(v_a_4605_);
v___x_4617_ = lean_box(0);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 1, v_a_4616_);
lean_ctor_set(v___x_4601_, 0, v___x_4617_);
v___x_4619_ = v___x_4601_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4617_);
lean_ctor_set(v_reuseFailAlloc_4623_, 1, v_a_4616_);
v___x_4619_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
size_t v___x_4620_; size_t v___x_4621_; 
v___x_4620_ = ((size_t)1ULL);
v___x_4621_ = lean_usize_add(v_i_4584_, v___x_4620_);
v_i_4584_ = v___x_4621_;
v_b_4585_ = v___x_4619_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_del_object(v___x_4601_);
lean_dec(v_snd_4599_);
v_a_4625_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4604_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4604_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object* v_init_4635_, lean_object* v_as_4636_, lean_object* v_sz_4637_, lean_object* v_i_4638_, lean_object* v_b_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_){
_start:
{
size_t v_sz_boxed_4651_; size_t v_i_boxed_4652_; lean_object* v_res_4653_; 
v_sz_boxed_4651_ = lean_unbox_usize(v_sz_4637_);
lean_dec(v_sz_4637_);
v_i_boxed_4652_ = lean_unbox_usize(v_i_4638_);
lean_dec(v_i_4638_);
v_res_4653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4635_, v_as_4636_, v_sz_boxed_4651_, v_i_boxed_4652_, v_b_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec(v___y_4640_);
lean_dec_ref(v_as_4636_);
lean_dec(v_init_4635_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_init_4654_, lean_object* v_n_4655_, lean_object* v_b_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4654_, v_n_4655_, v_b_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v_n_4655_);
lean_dec(v_init_4654_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_4669_, size_t v_sz_4670_, size_t v_i_4671_, lean_object* v_b_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
uint8_t v___x_4684_; 
v___x_4684_ = lean_usize_dec_lt(v_i_4671_, v_sz_4670_);
if (v___x_4684_ == 0)
{
lean_object* v___x_4685_; 
v___x_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4685_, 0, v_b_4672_);
return v___x_4685_;
}
else
{
lean_object* v_snd_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4710_; 
v_snd_4686_ = lean_ctor_get(v_b_4672_, 1);
v_isSharedCheck_4710_ = !lean_is_exclusive(v_b_4672_);
if (v_isSharedCheck_4710_ == 0)
{
lean_object* v_unused_4711_; 
v_unused_4711_ = lean_ctor_get(v_b_4672_, 0);
lean_dec(v_unused_4711_);
v___x_4688_ = v_b_4672_;
v_isShared_4689_ = v_isSharedCheck_4710_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_snd_4686_);
lean_dec(v_b_4672_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4710_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v_a_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v_a_4690_ = lean_array_uget_borrowed(v_as_4669_, v_i_4671_);
v___x_4691_ = lean_box(0);
v___x_4692_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4686_, v_a_4690_, v___x_4691_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; 
lean_dec_ref(v___x_4692_);
v___x_4693_ = lean_box(0);
v___x_4694_ = lean_unsigned_to_nat(1u);
v___x_4695_ = lean_nat_add(v_snd_4686_, v___x_4694_);
lean_dec(v_snd_4686_);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 1, v___x_4695_);
lean_ctor_set(v___x_4688_, 0, v___x_4693_);
v___x_4697_ = v___x_4688_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4701_, 1, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
size_t v___x_4698_; size_t v___x_4699_; 
v___x_4698_ = ((size_t)1ULL);
v___x_4699_ = lean_usize_add(v_i_4671_, v___x_4698_);
v_i_4671_ = v___x_4699_;
v_b_4672_ = v___x_4697_;
goto _start;
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_del_object(v___x_4688_);
lean_dec(v_snd_4686_);
v_a_4702_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4692_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4692_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_4712_, lean_object* v_sz_4713_, lean_object* v_i_4714_, lean_object* v_b_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
size_t v_sz_boxed_4727_; size_t v_i_boxed_4728_; lean_object* v_res_4729_; 
v_sz_boxed_4727_ = lean_unbox_usize(v_sz_4713_);
lean_dec(v_sz_4713_);
v_i_boxed_4728_ = lean_unbox_usize(v_i_4714_);
lean_dec(v_i_4714_);
v_res_4729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4712_, v_sz_boxed_4727_, v_i_boxed_4728_, v_b_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v_as_4712_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_4730_, size_t v_sz_4731_, size_t v_i_4732_, lean_object* v_b_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_){
_start:
{
uint8_t v___x_4745_; 
v___x_4745_ = lean_usize_dec_lt(v_i_4732_, v_sz_4731_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; 
v___x_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4746_, 0, v_b_4733_);
return v___x_4746_;
}
else
{
lean_object* v_snd_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4771_; 
v_snd_4747_ = lean_ctor_get(v_b_4733_, 1);
v_isSharedCheck_4771_ = !lean_is_exclusive(v_b_4733_);
if (v_isSharedCheck_4771_ == 0)
{
lean_object* v_unused_4772_; 
v_unused_4772_ = lean_ctor_get(v_b_4733_, 0);
lean_dec(v_unused_4772_);
v___x_4749_ = v_b_4733_;
v_isShared_4750_ = v_isSharedCheck_4771_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_snd_4747_);
lean_dec(v_b_4733_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4771_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v_a_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v_a_4751_ = lean_array_uget_borrowed(v_as_4730_, v_i_4732_);
v___x_4752_ = lean_box(0);
v___x_4753_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4747_, v_a_4751_, v___x_4752_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
lean_dec_ref(v___x_4753_);
v___x_4754_ = lean_box(0);
v___x_4755_ = lean_unsigned_to_nat(1u);
v___x_4756_ = lean_nat_add(v_snd_4747_, v___x_4755_);
lean_dec(v_snd_4747_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 1, v___x_4756_);
lean_ctor_set(v___x_4749_, 0, v___x_4754_);
v___x_4758_ = v___x_4749_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4754_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
size_t v___x_4759_; size_t v___x_4760_; lean_object* v___x_4761_; 
v___x_4759_ = ((size_t)1ULL);
v___x_4760_ = lean_usize_add(v_i_4732_, v___x_4759_);
v___x_4761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4730_, v_sz_4731_, v___x_4760_, v___x_4758_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
return v___x_4761_;
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_del_object(v___x_4749_);
lean_dec(v_snd_4747_);
v_a_4763_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4753_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4753_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_4773_, lean_object* v_sz_4774_, lean_object* v_i_4775_, lean_object* v_b_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
size_t v_sz_boxed_4788_; size_t v_i_boxed_4789_; lean_object* v_res_4790_; 
v_sz_boxed_4788_ = lean_unbox_usize(v_sz_4774_);
lean_dec(v_sz_4774_);
v_i_boxed_4789_ = lean_unbox_usize(v_i_4775_);
lean_dec(v_i_4775_);
v_res_4790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_as_4773_, v_sz_boxed_4788_, v_i_boxed_4789_, v_b_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec(v___y_4777_);
lean_dec_ref(v_as_4773_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(lean_object* v_t_4791_, lean_object* v_init_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v_root_4804_; lean_object* v_tail_4805_; lean_object* v___x_4806_; 
v_root_4804_ = lean_ctor_get(v_t_4791_, 0);
v_tail_4805_ = lean_ctor_get(v_t_4791_, 1);
lean_inc(v_init_4792_);
v___x_4806_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4792_, v_root_4804_, v_init_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
lean_dec(v_init_4792_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4843_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4843_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4843_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
if (lean_obj_tag(v_a_4807_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; 
v_a_4811_ = lean_ctor_get(v_a_4807_, 0);
lean_inc(v_a_4811_);
lean_dec_ref(v_a_4807_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v_a_4811_);
v___x_4813_ = v___x_4809_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4811_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
else
{
lean_object* v_a_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; size_t v_sz_4818_; size_t v___x_4819_; lean_object* v___x_4820_; 
lean_del_object(v___x_4809_);
v_a_4815_ = lean_ctor_get(v_a_4807_, 0);
lean_inc(v_a_4815_);
lean_dec_ref(v_a_4807_);
v___x_4816_ = lean_box(0);
v___x_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4816_);
lean_ctor_set(v___x_4817_, 1, v_a_4815_);
v_sz_4818_ = lean_array_size(v_tail_4805_);
v___x_4819_ = ((size_t)0ULL);
v___x_4820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_tail_4805_, v_sz_4818_, v___x_4819_, v___x_4817_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4834_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4823_ = v___x_4820_;
v_isShared_4824_ = v_isSharedCheck_4834_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4820_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4834_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v_fst_4825_; 
v_fst_4825_ = lean_ctor_get(v_a_4821_, 0);
if (lean_obj_tag(v_fst_4825_) == 0)
{
lean_object* v_snd_4826_; lean_object* v___x_4828_; 
v_snd_4826_ = lean_ctor_get(v_a_4821_, 1);
lean_inc(v_snd_4826_);
lean_dec(v_a_4821_);
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 0, v_snd_4826_);
v___x_4828_ = v___x_4823_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_snd_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
else
{
lean_object* v_val_4830_; lean_object* v___x_4832_; 
lean_inc_ref(v_fst_4825_);
lean_dec(v_a_4821_);
v_val_4830_ = lean_ctor_get(v_fst_4825_, 0);
lean_inc(v_val_4830_);
lean_dec_ref(v_fst_4825_);
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 0, v_val_4830_);
v___x_4832_ = v___x_4823_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_val_4830_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
v_a_4835_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4820_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4820_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
}
else
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
v_a_4844_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___x_4806_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4806_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_4852_, lean_object* v_init_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_t_4852_, v_init_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v_t_4852_);
return v_res_4865_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4868_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1));
v___x_4869_ = lean_unsigned_to_nat(2u);
v___x_4870_ = lean_unsigned_to_nat(103u);
v___x_4871_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0));
v___x_4872_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_4873_ = l_mkPanicMessageWithDecl(v___x_4872_, v___x_4871_, v___x_4870_, v___x_4869_, v___x_4868_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4874_, v_a_4882_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v_vars_4887_; lean_object* v_diseqs_4888_; lean_object* v_size_4889_; lean_object* v_size_4890_; uint8_t v___x_4891_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref(v___x_4885_);
v_vars_4887_ = lean_ctor_get(v_a_4886_, 0);
lean_inc_ref(v_vars_4887_);
v_diseqs_4888_ = lean_ctor_get(v_a_4886_, 9);
lean_inc_ref(v_diseqs_4888_);
lean_dec(v_a_4886_);
v_size_4889_ = lean_ctor_get(v_vars_4887_, 2);
lean_inc(v_size_4889_);
lean_dec_ref(v_vars_4887_);
v_size_4890_ = lean_ctor_get(v_diseqs_4888_, 2);
v___x_4891_ = lean_nat_dec_eq(v_size_4889_, v_size_4890_);
lean_dec(v_size_4889_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
lean_dec_ref(v_diseqs_4888_);
v___x_4892_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2);
v___x_4893_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_4892_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
return v___x_4893_;
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = lean_unsigned_to_nat(0u);
v___x_4895_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_diseqs_4888_, v___x_4894_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
lean_dec_ref(v_diseqs_4888_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4903_; 
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4903_ == 0)
{
lean_object* v_unused_4904_; 
v_unused_4904_ = lean_ctor_get(v___x_4895_, 0);
lean_dec(v_unused_4904_);
v___x_4897_ = v___x_4895_;
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
else
{
lean_dec(v___x_4895_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; lean_object* v___x_4901_; 
v___x_4899_ = lean_box(0);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v___x_4899_);
v___x_4901_ = v___x_4897_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
v_a_4905_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4895_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4895_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
v_a_4913_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4885_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4885_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___boxed(lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_){
_start:
{
lean_object* v___x_4944_; 
v___x_4944_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v___x_4945_; 
lean_dec_ref(v___x_4944_);
v___x_4945_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v___x_4946_; 
lean_dec_ref(v___x_4945_);
v___x_4946_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v___x_4947_; 
lean_dec_ref(v___x_4946_);
v___x_4947_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_object* v___x_4948_; 
lean_dec_ref(v___x_4947_);
v___x_4948_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v___x_4949_; 
lean_dec_ref(v___x_4948_);
v___x_4949_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v___x_4950_; 
lean_dec_ref(v___x_4949_);
v___x_4950_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
return v___x_4950_;
}
else
{
return v___x_4949_;
}
}
else
{
return v___x_4948_;
}
}
else
{
return v___x_4947_;
}
}
else
{
return v___x_4946_;
}
}
else
{
return v___x_4945_;
}
}
else
{
return v___x_4944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec(v_a_4951_);
return v_res_4962_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
}
#ifdef __cplusplus
}
#endif
