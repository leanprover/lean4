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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_1598__overap_28_ = lean_panic_fn(v___x_27_, v_msg_15_);
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
v___x_3991__overap_309_ = lean_panic_fn(v___x_308_, v_msg_296_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(lean_object* v_____s_796_, uint8_t v_isLower_797_, lean_object* v_inh_798_, lean_object* v_n_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
if (lean_obj_tag(v_n_799_) == 0)
{
lean_object* v_cs_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_846_; 
v_cs_812_ = lean_ctor_get(v_n_799_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_n_799_);
if (v_isSharedCheck_846_ == 0)
{
v___x_814_ = v_n_799_;
v_isShared_815_ = v_isSharedCheck_846_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_cs_812_);
lean_dec(v_n_799_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_846_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; size_t v_sz_818_; size_t v___x_819_; lean_object* v___x_820_; 
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_b_800_);
v_sz_818_ = lean_array_size(v_cs_812_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_____s_796_, v_isLower_797_, v_inh_798_, v_cs_812_, v_sz_818_, v___x_819_, v___x_817_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref(v_cs_812_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_837_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_837_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_837_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_837_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_fst_825_; 
v_fst_825_ = lean_ctor_get(v_a_821_, 0);
if (lean_obj_tag(v_fst_825_) == 0)
{
lean_object* v_snd_826_; lean_object* v___x_828_; 
v_snd_826_ = lean_ctor_get(v_a_821_, 1);
lean_inc(v_snd_826_);
lean_dec(v_a_821_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 1);
lean_ctor_set(v___x_814_, 0, v_snd_826_);
v___x_828_ = v___x_814_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_snd_826_);
v___x_828_ = v_reuseFailAlloc_832_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_830_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_828_);
v___x_830_ = v___x_823_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
lean_object* v_val_833_; lean_object* v___x_835_; 
lean_inc_ref(v_fst_825_);
lean_dec(v_a_821_);
lean_del_object(v___x_814_);
v_val_833_ = lean_ctor_get(v_fst_825_, 0);
lean_inc(v_val_833_);
lean_dec_ref(v_fst_825_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_val_833_);
v___x_835_ = v___x_823_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_val_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_del_object(v___x_814_);
v_a_838_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_820_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_820_);
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
}
else
{
lean_object* v_vs_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_881_; 
v_vs_847_ = lean_ctor_get(v_n_799_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_n_799_);
if (v_isSharedCheck_881_ == 0)
{
v___x_849_ = v_n_799_;
v_isShared_850_ = v_isSharedCheck_881_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_vs_847_);
lean_dec(v_n_799_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_881_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; size_t v_sz_853_; size_t v___x_854_; lean_object* v___x_855_; 
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v_b_800_);
v_sz_853_ = lean_array_size(v_vs_847_);
v___x_854_ = ((size_t)0ULL);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_796_, v_isLower_797_, v_vs_847_, v_sz_853_, v___x_854_, v___x_852_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref(v_vs_847_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_872_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_872_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_872_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_872_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_fst_860_; 
v_fst_860_ = lean_ctor_get(v_a_856_, 0);
if (lean_obj_tag(v_fst_860_) == 0)
{
lean_object* v_snd_861_; lean_object* v___x_863_; 
v_snd_861_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_snd_861_);
lean_dec(v_a_856_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v_snd_861_);
v___x_863_ = v___x_849_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_snd_861_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_863_);
v___x_865_ = v___x_858_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_val_868_; lean_object* v___x_870_; 
lean_inc_ref(v_fst_860_);
lean_dec(v_a_856_);
lean_del_object(v___x_849_);
v_val_868_ = lean_ctor_get(v_fst_860_, 0);
lean_inc(v_val_868_);
lean_dec_ref(v_fst_860_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v_val_868_);
v___x_870_ = v___x_858_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_val_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_del_object(v___x_849_);
v_a_873_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_855_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_855_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_____s_882_, uint8_t v_isLower_883_, lean_object* v_inh_884_, lean_object* v_as_885_, size_t v_sz_886_, size_t v_i_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = lean_usize_dec_lt(v_i_887_, v_sz_886_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_b_888_);
return v___x_901_;
}
else
{
lean_object* v_snd_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_936_; 
v_snd_902_ = lean_ctor_get(v_b_888_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_b_888_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v_b_888_, 0);
lean_dec(v_unused_937_);
v___x_904_ = v_b_888_;
v_isShared_905_ = v_isSharedCheck_936_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_snd_902_);
lean_dec(v_b_888_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_936_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_a_906_; lean_object* v___x_907_; 
v_a_906_ = lean_array_uget_borrowed(v_as_885_, v_i_887_);
lean_inc(v_snd_902_);
lean_inc(v_a_906_);
v___x_907_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_____s_882_, v_isLower_883_, v_inh_884_, v_a_906_, v_snd_902_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_927_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_927_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_927_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_927_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
if (lean_obj_tag(v_a_908_) == 0)
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_a_908_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_912_);
v___x_914_ = v___x_904_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_902_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_914_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
lean_del_object(v___x_910_);
lean_dec(v_snd_902_);
v_a_919_ = lean_ctor_get(v_a_908_, 0);
lean_inc(v_a_919_);
lean_dec_ref(v_a_908_);
v___x_920_ = lean_box(0);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_a_919_);
lean_ctor_set(v___x_904_, 0, v___x_920_);
v___x_922_ = v___x_904_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_a_919_);
v___x_922_ = v_reuseFailAlloc_926_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
size_t v___x_923_; size_t v___x_924_; 
v___x_923_ = ((size_t)1ULL);
v___x_924_ = lean_usize_add(v_i_887_, v___x_923_);
v_i_887_ = v___x_924_;
v_b_888_ = v___x_922_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_del_object(v___x_904_);
lean_dec(v_snd_902_);
v_a_928_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_907_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_907_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_938_ = _args[0];
lean_object* v_isLower_939_ = _args[1];
lean_object* v_inh_940_ = _args[2];
lean_object* v_as_941_ = _args[3];
lean_object* v_sz_942_ = _args[4];
lean_object* v_i_943_ = _args[5];
lean_object* v_b_944_ = _args[6];
lean_object* v___y_945_ = _args[7];
lean_object* v___y_946_ = _args[8];
lean_object* v___y_947_ = _args[9];
lean_object* v___y_948_ = _args[10];
lean_object* v___y_949_ = _args[11];
lean_object* v___y_950_ = _args[12];
lean_object* v___y_951_ = _args[13];
lean_object* v___y_952_ = _args[14];
lean_object* v___y_953_ = _args[15];
lean_object* v___y_954_ = _args[16];
lean_object* v___y_955_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_956_; size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_isLower_boxed_956_ = lean_unbox(v_isLower_939_);
v_sz_boxed_957_ = lean_unbox_usize(v_sz_942_);
lean_dec(v_sz_942_);
v_i_boxed_958_ = lean_unbox_usize(v_i_943_);
lean_dec(v_i_943_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_____s_938_, v_isLower_boxed_956_, v_inh_940_, v_as_941_, v_sz_boxed_957_, v_i_boxed_958_, v_b_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v_as_941_);
lean_dec(v_____s_938_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1___boxed(lean_object* v_____s_960_, lean_object* v_isLower_961_, lean_object* v_inh_962_, lean_object* v_n_963_, lean_object* v_b_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v_isLower_boxed_976_; lean_object* v_res_977_; 
v_isLower_boxed_976_ = lean_unbox(v_isLower_961_);
v_res_977_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_____s_960_, v_isLower_boxed_976_, v_inh_962_, v_n_963_, v_b_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v_____s_960_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(lean_object* v_____s_978_, uint8_t v_isLower_979_, lean_object* v_t_980_, lean_object* v_init_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_root_993_; lean_object* v_tail_994_; lean_object* v___x_995_; 
v_root_993_ = lean_ctor_get(v_t_980_, 0);
lean_inc_ref(v_root_993_);
v_tail_994_ = lean_ctor_get(v_t_980_, 1);
lean_inc_ref(v_tail_994_);
lean_dec_ref(v_t_980_);
v___x_995_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_____s_978_, v_isLower_979_, v_init_981_, v_root_993_, v_init_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1032_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1032_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1032_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
if (lean_obj_tag(v_a_996_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; 
lean_dec_ref(v_tail_994_);
v_a_1000_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v_a_996_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v_a_1000_);
v___x_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; size_t v_sz_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
lean_del_object(v___x_998_);
v_a_1004_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v_a_996_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v_a_1004_);
v_sz_1007_ = lean_array_size(v_tail_994_);
v___x_1008_ = ((size_t)0ULL);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_978_, v_isLower_979_, v_tail_994_, v_sz_1007_, v___x_1008_, v___x_1006_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec_ref(v_tail_994_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1023_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1023_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1023_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_fst_1014_; 
v_fst_1014_ = lean_ctor_get(v_a_1010_, 0);
if (lean_obj_tag(v_fst_1014_) == 0)
{
lean_object* v_snd_1015_; lean_object* v___x_1017_; 
v_snd_1015_ = lean_ctor_get(v_a_1010_, 1);
lean_inc(v_snd_1015_);
lean_dec(v_a_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v_snd_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_snd_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
lean_object* v_val_1019_; lean_object* v___x_1021_; 
lean_inc_ref(v_fst_1014_);
lean_dec(v_a_1010_);
v_val_1019_ = lean_ctor_get(v_fst_1014_, 0);
lean_inc(v_val_1019_);
lean_dec_ref(v_fst_1014_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v_val_1019_);
v___x_1021_ = v___x_1012_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_val_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1009_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1009_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_tail_994_);
v_a_1033_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_995_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_995_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1041_, lean_object* v_isLower_1042_, lean_object* v_t_1043_, lean_object* v_init_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v_isLower_boxed_1056_; lean_object* v_res_1057_; 
v_isLower_boxed_1056_ = lean_unbox(v_isLower_1042_);
v_res_1057_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_____s_1041_, v_isLower_boxed_1056_, v_t_1043_, v_init_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v_____s_1041_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1058_, lean_object* v_as_1059_, size_t v_sz_1060_, size_t v_i_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_usize_dec_lt(v_i_1061_, v_sz_1060_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_b_1062_);
return v___x_1075_;
}
else
{
lean_object* v_snd_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1100_; 
v_snd_1076_ = lean_ctor_get(v_b_1062_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_b_1062_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v_b_1062_, 0);
lean_dec(v_unused_1101_);
v___x_1078_ = v_b_1062_;
v_isShared_1079_ = v_isSharedCheck_1100_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_snd_1076_);
lean_dec(v_b_1062_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1100_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_a_1080_ = lean_array_uget_borrowed(v_as_1059_, v_i_1061_);
v___x_1081_ = lean_box(0);
lean_inc(v_a_1080_);
v___x_1082_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1076_, v_isLower_1058_, v_a_1080_, v___x_1081_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_dec_ref(v___x_1082_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_unsigned_to_nat(1u);
v___x_1085_ = lean_nat_add(v_snd_1076_, v___x_1084_);
lean_dec(v_snd_1076_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v___x_1085_);
lean_ctor_set(v___x_1078_, 0, v___x_1083_);
v___x_1087_ = v___x_1078_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
size_t v___x_1088_; size_t v___x_1089_; 
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1061_, v___x_1088_);
v_i_1061_ = v___x_1089_;
v_b_1062_ = v___x_1087_;
goto _start;
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_del_object(v___x_1078_);
lean_dec(v_snd_1076_);
v_a_1092_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1082_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1082_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object* v_isLower_1102_, lean_object* v_as_1103_, lean_object* v_sz_1104_, lean_object* v_i_1105_, lean_object* v_b_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_isLower_boxed_1118_; size_t v_sz_boxed_1119_; size_t v_i_boxed_1120_; lean_object* v_res_1121_; 
v_isLower_boxed_1118_ = lean_unbox(v_isLower_1102_);
v_sz_boxed_1119_ = lean_unbox_usize(v_sz_1104_);
lean_dec(v_sz_1104_);
v_i_boxed_1120_ = lean_unbox_usize(v_i_1105_);
lean_dec(v_i_1105_);
v_res_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_1118_, v_as_1103_, v_sz_boxed_1119_, v_i_boxed_1120_, v_b_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v_as_1103_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1122_, lean_object* v_as_1123_, size_t v_sz_1124_, size_t v_i_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = lean_usize_dec_lt(v_i_1125_, v_sz_1124_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_b_1126_);
return v___x_1139_;
}
else
{
lean_object* v_snd_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1164_; 
v_snd_1140_ = lean_ctor_get(v_b_1126_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_b_1126_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v_b_1126_, 0);
lean_dec(v_unused_1165_);
v___x_1142_ = v_b_1126_;
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_snd_1140_);
lean_dec(v_b_1126_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_a_1144_ = lean_array_uget_borrowed(v_as_1123_, v_i_1125_);
v___x_1145_ = lean_box(0);
lean_inc(v_a_1144_);
v___x_1146_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1140_, v_isLower_1122_, v_a_1144_, v___x_1145_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec_ref(v___x_1146_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_snd_1140_, v___x_1148_);
lean_dec(v_snd_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1149_);
lean_ctor_set(v___x_1142_, 0, v___x_1147_);
v___x_1151_ = v___x_1142_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = ((size_t)1ULL);
v___x_1153_ = lean_usize_add(v_i_1125_, v___x_1152_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1122_, v_as_1123_, v_sz_1124_, v___x_1153_, v___x_1151_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1154_;
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_del_object(v___x_1142_);
lean_dec(v_snd_1140_);
v_a_1156_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1146_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1146_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5___boxed(lean_object* v_isLower_1166_, lean_object* v_as_1167_, lean_object* v_sz_1168_, lean_object* v_i_1169_, lean_object* v_b_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v_isLower_boxed_1182_; size_t v_sz_boxed_1183_; size_t v_i_boxed_1184_; lean_object* v_res_1185_; 
v_isLower_boxed_1182_ = lean_unbox(v_isLower_1166_);
v_sz_boxed_1183_ = lean_unbox_usize(v_sz_1168_);
lean_dec(v_sz_1168_);
v_i_boxed_1184_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1182_, v_as_1167_, v_sz_boxed_1183_, v_i_boxed_1184_, v_b_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v_as_1167_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1186_, lean_object* v_as_1187_, size_t v_sz_1188_, size_t v_i_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_usize_dec_lt(v_i_1189_, v_sz_1188_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v_b_1190_);
return v___x_1203_;
}
else
{
lean_object* v_snd_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1228_; 
v_snd_1204_ = lean_ctor_get(v_b_1190_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_b_1190_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v_b_1190_, 0);
lean_dec(v_unused_1229_);
v___x_1206_ = v_b_1190_;
v_isShared_1207_ = v_isSharedCheck_1228_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_snd_1204_);
lean_dec(v_b_1190_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1228_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_a_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_a_1208_ = lean_array_uget_borrowed(v_as_1187_, v_i_1189_);
v___x_1209_ = lean_box(0);
lean_inc(v_a_1208_);
v___x_1210_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1204_, v_isLower_1186_, v_a_1208_, v___x_1209_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_dec_ref(v___x_1210_);
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_add(v_snd_1204_, v___x_1212_);
lean_dec(v_snd_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1213_);
lean_ctor_set(v___x_1206_, 0, v___x_1211_);
v___x_1215_ = v___x_1206_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
size_t v___x_1216_; size_t v___x_1217_; 
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_add(v_i_1189_, v___x_1216_);
v_i_1189_ = v___x_1217_;
v_b_1190_ = v___x_1215_;
goto _start;
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_1206_);
lean_dec(v_snd_1204_);
v_a_1220_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1210_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1210_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object* v_isLower_1230_, lean_object* v_as_1231_, lean_object* v_sz_1232_, lean_object* v_i_1233_, lean_object* v_b_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v_isLower_boxed_1246_; size_t v_sz_boxed_1247_; size_t v_i_boxed_1248_; lean_object* v_res_1249_; 
v_isLower_boxed_1246_ = lean_unbox(v_isLower_1230_);
v_sz_boxed_1247_ = lean_unbox_usize(v_sz_1232_);
lean_dec(v_sz_1232_);
v_i_boxed_1248_ = lean_unbox_usize(v_i_1233_);
lean_dec(v_i_1233_);
v_res_1249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1246_, v_as_1231_, v_sz_boxed_1247_, v_i_boxed_1248_, v_b_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v_as_1231_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1250_, lean_object* v_as_1251_, size_t v_sz_1252_, size_t v_i_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_lt(v_i_1253_, v_sz_1252_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1254_);
return v___x_1267_;
}
else
{
lean_object* v_snd_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1292_; 
v_snd_1268_ = lean_ctor_get(v_b_1254_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_b_1254_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v_b_1254_, 0);
lean_dec(v_unused_1293_);
v___x_1270_ = v_b_1254_;
v_isShared_1271_ = v_isSharedCheck_1292_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_snd_1268_);
lean_dec(v_b_1254_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1292_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_array_uget_borrowed(v_as_1251_, v_i_1253_);
v___x_1273_ = lean_box(0);
lean_inc(v_a_1272_);
v___x_1274_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1268_, v_isLower_1250_, v_a_1272_, v___x_1273_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_dec_ref(v___x_1274_);
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_add(v_snd_1268_, v___x_1276_);
lean_dec(v_snd_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1277_);
lean_ctor_set(v___x_1270_, 0, v___x_1275_);
v___x_1279_ = v___x_1270_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1253_, v___x_1280_);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1250_, v_as_1251_, v_sz_1252_, v___x_1281_, v___x_1279_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1282_;
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_del_object(v___x_1270_);
lean_dec(v_snd_1268_);
v_a_1284_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1274_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1274_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object* v_isLower_1294_, lean_object* v_as_1295_, lean_object* v_sz_1296_, lean_object* v_i_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v_isLower_boxed_1310_; size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_isLower_boxed_1310_ = lean_unbox(v_isLower_1294_);
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1310_, v_as_1295_, v_sz_boxed_1311_, v_i_boxed_1312_, v_b_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v_as_1295_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(uint8_t v_isLower_1314_, lean_object* v_inh_1315_, lean_object* v_n_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
if (lean_obj_tag(v_n_1316_) == 0)
{
lean_object* v_cs_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1363_; 
v_cs_1329_ = lean_ctor_get(v_n_1316_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_n_1316_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1331_ = v_n_1316_;
v_isShared_1332_ = v_isSharedCheck_1363_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_cs_1329_);
lean_dec(v_n_1316_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1363_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; size_t v_sz_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v_b_1317_);
v_sz_1335_ = lean_array_size(v_cs_1329_);
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_isLower_1314_, v_inh_1315_, v_cs_1329_, v_sz_1335_, v___x_1336_, v___x_1334_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec_ref(v_cs_1329_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1354_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1354_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1354_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_fst_1342_; 
v_fst_1342_ = lean_ctor_get(v_a_1338_, 0);
if (lean_obj_tag(v_fst_1342_) == 0)
{
lean_object* v_snd_1343_; lean_object* v___x_1345_; 
v_snd_1343_ = lean_ctor_get(v_a_1338_, 1);
lean_inc(v_snd_1343_);
lean_dec(v_a_1338_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set_tag(v___x_1331_, 1);
lean_ctor_set(v___x_1331_, 0, v_snd_1343_);
v___x_1345_ = v___x_1331_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_snd_1343_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1345_);
v___x_1347_ = v___x_1340_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
lean_object* v_val_1350_; lean_object* v___x_1352_; 
lean_inc_ref(v_fst_1342_);
lean_dec(v_a_1338_);
lean_del_object(v___x_1331_);
v_val_1350_ = lean_ctor_get(v_fst_1342_, 0);
lean_inc(v_val_1350_);
lean_dec_ref(v_fst_1342_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_val_1350_);
v___x_1352_ = v___x_1340_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_val_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_del_object(v___x_1331_);
v_a_1355_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1337_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1337_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
else
{
lean_object* v_vs_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1398_; 
v_vs_1364_ = lean_ctor_get(v_n_1316_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_n_1316_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1366_ = v_n_1316_;
v_isShared_1367_ = v_isSharedCheck_1398_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_vs_1364_);
lean_dec(v_n_1316_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1398_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; size_t v_sz_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v_b_1317_);
v_sz_1370_ = lean_array_size(v_vs_1364_);
v___x_1371_ = ((size_t)0ULL);
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1314_, v_vs_1364_, v_sz_1370_, v___x_1371_, v___x_1369_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec_ref(v_vs_1364_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1389_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1389_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1389_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_fst_1377_; 
v_fst_1377_ = lean_ctor_get(v_a_1373_, 0);
if (lean_obj_tag(v_fst_1377_) == 0)
{
lean_object* v_snd_1378_; lean_object* v___x_1380_; 
v_snd_1378_ = lean_ctor_get(v_a_1373_, 1);
lean_inc(v_snd_1378_);
lean_dec(v_a_1373_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v_snd_1378_);
v___x_1380_ = v___x_1366_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_snd_1378_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1380_);
v___x_1382_ = v___x_1375_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_object* v_val_1385_; lean_object* v___x_1387_; 
lean_inc_ref(v_fst_1377_);
lean_dec(v_a_1373_);
lean_del_object(v___x_1366_);
v_val_1385_ = lean_ctor_get(v_fst_1377_, 0);
lean_inc(v_val_1385_);
lean_dec_ref(v_fst_1377_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_val_1385_);
v___x_1387_ = v___x_1375_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_val_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_del_object(v___x_1366_);
v_a_1390_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1372_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1372_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(uint8_t v_isLower_1399_, lean_object* v_inh_1400_, lean_object* v_as_1401_, size_t v_sz_1402_, size_t v_i_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_usize_dec_lt(v_i_1403_, v_sz_1402_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_b_1404_);
return v___x_1417_;
}
else
{
lean_object* v_snd_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1452_; 
v_snd_1418_ = lean_ctor_get(v_b_1404_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_b_1404_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_b_1404_, 0);
lean_dec(v_unused_1453_);
v___x_1420_ = v_b_1404_;
v_isShared_1421_ = v_isSharedCheck_1452_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_snd_1418_);
lean_dec(v_b_1404_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1452_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_array_uget_borrowed(v_as_1401_, v_i_1403_);
lean_inc(v_snd_1418_);
lean_inc(v_a_1422_);
v___x_1423_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_isLower_1399_, v_inh_1400_, v_a_1422_, v_snd_1418_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1443_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1443_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1443_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
if (lean_obj_tag(v_a_1424_) == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_a_1424_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1428_);
v___x_1430_ = v___x_1420_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_snd_1418_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1432_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1430_);
v___x_1432_ = v___x_1426_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_del_object(v___x_1426_);
lean_dec(v_snd_1418_);
v_a_1435_ = lean_ctor_get(v_a_1424_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v_a_1424_);
v___x_1436_ = lean_box(0);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v_a_1435_);
lean_ctor_set(v___x_1420_, 0, v___x_1436_);
v___x_1438_ = v___x_1420_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_a_1435_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
size_t v___x_1439_; size_t v___x_1440_; 
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_i_1403_, v___x_1439_);
v_i_1403_ = v___x_1440_;
v_b_1404_ = v___x_1438_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_del_object(v___x_1420_);
lean_dec(v_snd_1418_);
v_a_1444_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1423_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1423_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_isLower_1454_ = _args[0];
lean_object* v_inh_1455_ = _args[1];
lean_object* v_as_1456_ = _args[2];
lean_object* v_sz_1457_ = _args[3];
lean_object* v_i_1458_ = _args[4];
lean_object* v_b_1459_ = _args[5];
lean_object* v___y_1460_ = _args[6];
lean_object* v___y_1461_ = _args[7];
lean_object* v___y_1462_ = _args[8];
lean_object* v___y_1463_ = _args[9];
lean_object* v___y_1464_ = _args[10];
lean_object* v___y_1465_ = _args[11];
lean_object* v___y_1466_ = _args[12];
lean_object* v___y_1467_ = _args[13];
lean_object* v___y_1468_ = _args[14];
lean_object* v___y_1469_ = _args[15];
lean_object* v___y_1470_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1471_; size_t v_sz_boxed_1472_; size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_isLower_boxed_1471_ = lean_unbox(v_isLower_1454_);
v_sz_boxed_1472_ = lean_unbox_usize(v_sz_1457_);
lean_dec(v_sz_1457_);
v_i_boxed_1473_ = lean_unbox_usize(v_i_1458_);
lean_dec(v_i_1458_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_isLower_boxed_1471_, v_inh_1455_, v_as_1456_, v_sz_boxed_1472_, v_i_boxed_1473_, v_b_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v_as_1456_);
lean_dec(v_inh_1455_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_isLower_1475_, lean_object* v_inh_1476_, lean_object* v_n_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_isLower_boxed_1490_; lean_object* v_res_1491_; 
v_isLower_boxed_1490_ = lean_unbox(v_isLower_1475_);
v_res_1491_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_isLower_boxed_1490_, v_inh_1476_, v_n_1477_, v_b_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec(v_inh_1476_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(uint8_t v_isLower_1492_, lean_object* v_t_1493_, lean_object* v_init_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_root_1506_; lean_object* v_tail_1507_; lean_object* v___x_1508_; 
v_root_1506_ = lean_ctor_get(v_t_1493_, 0);
lean_inc_ref(v_root_1506_);
v_tail_1507_ = lean_ctor_get(v_t_1493_, 1);
lean_inc_ref(v_tail_1507_);
lean_dec_ref(v_t_1493_);
lean_inc(v_init_1494_);
v___x_1508_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_isLower_1492_, v_init_1494_, v_root_1506_, v_init_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v_init_1494_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1545_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1545_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1545_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
if (lean_obj_tag(v_a_1509_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; 
lean_dec_ref(v_tail_1507_);
v_a_1513_ = lean_ctor_get(v_a_1509_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v_a_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v_a_1513_);
v___x_1515_ = v___x_1511_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
lean_del_object(v___x_1511_);
v_a_1517_ = lean_ctor_get(v_a_1509_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v_a_1509_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v_a_1517_);
v_sz_1520_ = lean_array_size(v_tail_1507_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_1492_, v_tail_1507_, v_sz_1520_, v___x_1521_, v___x_1519_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec_ref(v_tail_1507_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1536_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1536_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1536_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_fst_1527_; 
v_fst_1527_ = lean_ctor_get(v_a_1523_, 0);
if (lean_obj_tag(v_fst_1527_) == 0)
{
lean_object* v_snd_1528_; lean_object* v___x_1530_; 
v_snd_1528_ = lean_ctor_get(v_a_1523_, 1);
lean_inc(v_snd_1528_);
lean_dec(v_a_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_snd_1528_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_snd_1528_);
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
lean_object* v_val_1532_; lean_object* v___x_1534_; 
lean_inc_ref(v_fst_1527_);
lean_dec(v_a_1523_);
v_val_1532_ = lean_ctor_get(v_fst_1527_, 0);
lean_inc(v_val_1532_);
lean_dec_ref(v_fst_1527_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_val_1532_);
v___x_1534_ = v___x_1525_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_val_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1537_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1522_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1522_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v_tail_1507_);
v_a_1546_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1508_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1508_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1554_, lean_object* v_t_1555_, lean_object* v_init_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v_isLower_boxed_1568_; lean_object* v_res_1569_; 
v_isLower_boxed_1568_ = lean_unbox(v_isLower_1554_);
v_res_1569_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_boxed_1568_, v_t_1555_, v_init_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(lean_object* v_css_1570_, uint8_t v_isLower_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_x_1583_; lean_object* v___x_1584_; 
v_x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_1571_, v_css_1570_, v_x_1583_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1592_; 
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v___x_1584_, 0);
lean_dec(v_unused_1593_);
v___x_1586_ = v___x_1584_;
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v___x_1584_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_box(0);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_a_1594_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1584_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1584_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs___boxed(lean_object* v_css_1602_, lean_object* v_isLower_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
uint8_t v_isLower_boxed_1615_; lean_object* v_res_1616_; 
v_isLower_boxed_1615_ = lean_unbox(v_isLower_1603_);
v_res_1616_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_css_1602_, v_isLower_boxed_1615_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec(v_a_1604_);
return v_res_1616_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1619_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1));
v___x_1620_ = lean_unsigned_to_nat(2u);
v___x_1621_ = lean_unsigned_to_nat(55u);
v___x_1622_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0));
v___x_1623_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_1624_ = l_mkPanicMessageWithDecl(v___x_1623_, v___x_1622_, v___x_1621_, v___x_1620_, v___x_1619_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1625_, v_a_1633_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v_lowers_1638_; lean_object* v_vars_1639_; lean_object* v_size_1640_; lean_object* v_size_1641_; uint8_t v___x_1642_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v___x_1636_);
v_lowers_1638_ = lean_ctor_get(v_a_1637_, 7);
lean_inc_ref(v_lowers_1638_);
v_vars_1639_ = lean_ctor_get(v_a_1637_, 0);
lean_inc_ref(v_vars_1639_);
lean_dec(v_a_1637_);
v_size_1640_ = lean_ctor_get(v_lowers_1638_, 2);
v_size_1641_ = lean_ctor_get(v_vars_1639_, 2);
lean_inc(v_size_1641_);
lean_dec_ref(v_vars_1639_);
v___x_1642_ = lean_nat_dec_eq(v_size_1640_, v_size_1641_);
lean_dec(v_size_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec_ref(v_lowers_1638_);
v___x_1643_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2);
v___x_1644_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_1643_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_lowers_1638_, v___x_1642_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
return v___x_1645_;
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_a_1646_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1636_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1636_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___boxed(lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec(v_a_1654_);
return v_res_1665_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1668_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1));
v___x_1669_ = lean_unsigned_to_nat(2u);
v___x_1670_ = lean_unsigned_to_nat(60u);
v___x_1671_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0));
v___x_1672_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_1673_ = l_mkPanicMessageWithDecl(v___x_1672_, v___x_1671_, v___x_1670_, v___x_1669_, v___x_1668_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1674_, v_a_1682_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v_uppers_1687_; lean_object* v_vars_1688_; lean_object* v_size_1689_; lean_object* v_size_1690_; uint8_t v___x_1691_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1685_);
v_uppers_1687_ = lean_ctor_get(v_a_1686_, 8);
lean_inc_ref(v_uppers_1687_);
v_vars_1688_ = lean_ctor_get(v_a_1686_, 0);
lean_inc_ref(v_vars_1688_);
lean_dec(v_a_1686_);
v_size_1689_ = lean_ctor_get(v_uppers_1687_, 2);
v_size_1690_ = lean_ctor_get(v_vars_1688_, 2);
lean_inc(v_size_1690_);
lean_dec_ref(v_vars_1688_);
v___x_1691_ = lean_nat_dec_eq(v_size_1689_, v_size_1690_);
lean_dec(v_size_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec_ref(v_uppers_1687_);
v___x_1692_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2);
v___x_1693_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_1692_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1693_;
}
else
{
uint8_t v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = 0;
v___x_1695_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_uppers_1687_, v___x_1694_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1695_;
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_a_1696_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1685_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1685_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___boxed(lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec(v_a_1704_);
return v_res_1715_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_4873__overap_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0);
v___x_4873__overap_1730_ = lean_panic_fn(v___x_1729_, v_msg_1717_);
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1726_);
lean_inc(v___y_1725_);
lean_inc_ref(v___y_1724_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
lean_inc(v___y_1719_);
lean_inc(v___y_1718_);
v___x_1731_ = lean_apply_11(v___x_4873__overap_1730_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, lean_box(0));
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___boxed(lean_object* v_msg_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v_msg_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec(v___y_1733_);
return v_res_1744_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_to_int(v___x_1745_);
return v___x_1746_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2));
v___x_1750_ = lean_unsigned_to_nat(6u);
v___x_1751_ = lean_unsigned_to_nat(70u);
v___x_1752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_1753_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_1754_ = l_mkPanicMessageWithDecl(v___x_1753_, v___x_1752_, v___x_1751_, v___x_1750_, v___x_1749_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1755_, size_t v_sz_1756_, size_t v_i_1757_, lean_object* v_b_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_lt(v_i_1757_, v_sz_1756_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_b_1758_);
return v___x_1771_;
}
else
{
lean_object* v_snd_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1830_; 
v_snd_1772_ = lean_ctor_get(v_b_1758_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_b_1758_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v_b_1758_, 0);
lean_dec(v_unused_1831_);
v___x_1774_ = v_b_1758_;
v_isShared_1775_ = v_isSharedCheck_1830_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_snd_1772_);
lean_dec(v_b_1758_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1830_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v_a_1778_; lean_object* v_a_1788_; 
v___x_1776_ = lean_box(0);
v_a_1788_ = lean_array_uget(v_as_1755_, v_i_1757_);
if (lean_obj_tag(v_a_1788_) == 1)
{
lean_object* v_val_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1829_; 
v_val_1789_ = lean_ctor_get(v_a_1788_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_a_1788_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1791_ = v_a_1788_;
v_isShared_1792_ = v_isSharedCheck_1829_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_val_1789_);
lean_dec(v_a_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1829_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_d_1793_; lean_object* v_p_1794_; lean_object* v___x_1795_; 
v_d_1793_ = lean_ctor_get(v_val_1789_, 0);
lean_inc(v_d_1793_);
v_p_1794_ = lean_ctor_get(v_val_1789_, 1);
lean_inc_ref(v_p_1794_);
lean_dec(v_val_1789_);
v___x_1795_ = l_Int_Linear_Poly_checkCnstrOf(v_p_1794_, v_snd_1772_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec_ref(v_p_1794_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
lean_dec_ref(v___x_1795_);
v___x_1796_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1797_ = lean_int_dec_lt(v___x_1796_, v_d_1793_);
lean_dec(v_d_1793_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1799_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1798_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1812_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1812_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1812_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
if (lean_obj_tag(v_a_1800_) == 0)
{
lean_object* v___x_1805_; 
lean_del_object(v___x_1774_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_a_1800_);
v___x_1805_ = v___x_1791_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v_snd_1772_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1806_);
v___x_1808_ = v___x_1802_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
else
{
lean_object* v_a_1811_; 
lean_del_object(v___x_1802_);
lean_del_object(v___x_1791_);
lean_dec(v_snd_1772_);
v_a_1811_ = lean_ctor_get(v_a_1800_, 0);
lean_inc(v_a_1811_);
lean_dec_ref(v_a_1800_);
v_a_1778_ = v_a_1811_;
goto v___jp_1777_;
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_del_object(v___x_1791_);
lean_del_object(v___x_1774_);
lean_dec(v_snd_1772_);
v_a_1813_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1799_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1799_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_del_object(v___x_1791_);
goto v___jp_1785_;
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_d_1793_);
lean_del_object(v___x_1791_);
lean_del_object(v___x_1774_);
lean_dec(v_snd_1772_);
v_a_1821_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1795_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1795_);
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
else
{
lean_dec(v_a_1788_);
goto v___jp_1785_;
}
v___jp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_a_1778_);
lean_ctor_set(v___x_1774_, 0, v___x_1776_);
v___x_1780_ = v___x_1774_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_a_1778_);
v___x_1780_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
size_t v___x_1781_; size_t v___x_1782_; 
v___x_1781_ = ((size_t)1ULL);
v___x_1782_ = lean_usize_add(v_i_1757_, v___x_1781_);
v_i_1757_ = v___x_1782_;
v_b_1758_ = v___x_1780_;
goto _start;
}
}
v___jp_1785_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = lean_nat_add(v_snd_1772_, v___x_1786_);
lean_dec(v_snd_1772_);
v_a_1778_ = v___x_1787_;
goto v___jp_1777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1832_, lean_object* v_sz_1833_, lean_object* v_i_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
size_t v_sz_boxed_1847_; size_t v_i_boxed_1848_; lean_object* v_res_1849_; 
v_sz_boxed_1847_ = lean_unbox_usize(v_sz_1833_);
lean_dec(v_sz_1833_);
v_i_boxed_1848_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1832_, v_sz_boxed_1847_, v_i_boxed_1848_, v_b_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v_as_1832_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(lean_object* v_as_1850_, size_t v_sz_1851_, size_t v_i_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_usize_dec_lt(v_i_1852_, v_sz_1851_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_b_1853_);
return v___x_1866_;
}
else
{
lean_object* v_snd_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1925_; 
v_snd_1867_ = lean_ctor_get(v_b_1853_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_b_1853_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v_b_1853_, 0);
lean_dec(v_unused_1926_);
v___x_1869_ = v_b_1853_;
v_isShared_1870_ = v_isSharedCheck_1925_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snd_1867_);
lean_dec(v_b_1853_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1925_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v_a_1873_; lean_object* v_a_1883_; 
v___x_1871_ = lean_box(0);
v_a_1883_ = lean_array_uget(v_as_1850_, v_i_1852_);
if (lean_obj_tag(v_a_1883_) == 1)
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1924_; 
v_val_1884_ = lean_ctor_get(v_a_1883_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_a_1883_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1886_ = v_a_1883_;
v_isShared_1887_ = v_isSharedCheck_1924_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v_a_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1924_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_d_1888_; lean_object* v_p_1889_; lean_object* v___x_1890_; 
v_d_1888_ = lean_ctor_get(v_val_1884_, 0);
lean_inc(v_d_1888_);
v_p_1889_ = lean_ctor_get(v_val_1884_, 1);
lean_inc_ref(v_p_1889_);
lean_dec(v_val_1884_);
v___x_1890_ = l_Int_Linear_Poly_checkCnstrOf(v_p_1889_, v_snd_1867_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec_ref(v_p_1889_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
lean_dec_ref(v___x_1890_);
v___x_1891_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1892_ = lean_int_dec_lt(v___x_1891_, v_d_1888_);
lean_dec(v_d_1888_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1894_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1893_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1907_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1907_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1907_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
if (lean_obj_tag(v_a_1895_) == 0)
{
lean_object* v___x_1900_; 
lean_del_object(v___x_1869_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v_a_1895_);
v___x_1900_ = v___x_1886_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_snd_1867_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1901_);
v___x_1903_ = v___x_1897_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v_a_1906_; 
lean_del_object(v___x_1897_);
lean_del_object(v___x_1886_);
lean_dec(v_snd_1867_);
v_a_1906_ = lean_ctor_get(v_a_1895_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v_a_1895_);
v_a_1873_ = v_a_1906_;
goto v___jp_1872_;
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_del_object(v___x_1886_);
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
v_a_1908_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1894_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1894_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_del_object(v___x_1886_);
goto v___jp_1880_;
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_d_1888_);
lean_del_object(v___x_1886_);
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
v_a_1916_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1890_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1890_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
else
{
lean_dec(v_a_1883_);
goto v___jp_1880_;
}
v___jp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v_a_1873_);
lean_ctor_set(v___x_1869_, 0, v___x_1871_);
v___x_1875_ = v___x_1869_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_a_1873_);
v___x_1875_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
size_t v___x_1876_; size_t v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = ((size_t)1ULL);
v___x_1877_ = lean_usize_add(v_i_1852_, v___x_1876_);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1850_, v_sz_1851_, v___x_1877_, v___x_1875_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1878_;
}
}
v___jp_1880_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_unsigned_to_nat(1u);
v___x_1882_ = lean_nat_add(v_snd_1867_, v___x_1881_);
lean_dec(v_snd_1867_);
v_a_1873_ = v___x_1882_;
goto v___jp_1872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1927_, lean_object* v_sz_1928_, lean_object* v_i_1929_, lean_object* v_b_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
size_t v_sz_boxed_1942_; size_t v_i_boxed_1943_; lean_object* v_res_1944_; 
v_sz_boxed_1942_ = lean_unbox_usize(v_sz_1928_);
lean_dec(v_sz_1928_);
v_i_boxed_1943_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_res_1944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_as_1927_, v_sz_boxed_1942_, v_i_boxed_1943_, v_b_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v_as_1927_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(lean_object* v_inh_1945_, lean_object* v_n_1946_, lean_object* v_b_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
if (lean_obj_tag(v_n_1946_) == 0)
{
lean_object* v_cs_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1993_; 
v_cs_1959_ = lean_ctor_get(v_n_1946_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_n_1946_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1961_ = v_n_1946_;
v_isShared_1962_ = v_isSharedCheck_1993_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_cs_1959_);
lean_dec(v_n_1946_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1993_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; size_t v_sz_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v_b_1947_);
v_sz_1965_ = lean_array_size(v_cs_1959_);
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_inh_1945_, v_cs_1959_, v_sz_1965_, v___x_1966_, v___x_1964_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec_ref(v_cs_1959_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1984_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1984_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1984_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_fst_1972_; 
v_fst_1972_ = lean_ctor_get(v_a_1968_, 0);
if (lean_obj_tag(v_fst_1972_) == 0)
{
lean_object* v_snd_1973_; lean_object* v___x_1975_; 
v_snd_1973_ = lean_ctor_get(v_a_1968_, 1);
lean_inc(v_snd_1973_);
lean_dec(v_a_1968_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 1);
lean_ctor_set(v___x_1961_, 0, v_snd_1973_);
v___x_1975_ = v___x_1961_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_snd_1973_);
v___x_1975_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1977_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1975_);
v___x_1977_ = v___x_1970_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_val_1980_; lean_object* v___x_1982_; 
lean_inc_ref(v_fst_1972_);
lean_dec(v_a_1968_);
lean_del_object(v___x_1961_);
v_val_1980_ = lean_ctor_get(v_fst_1972_, 0);
lean_inc(v_val_1980_);
lean_dec_ref(v_fst_1972_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_val_1980_);
v___x_1982_ = v___x_1970_;
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
lean_del_object(v___x_1961_);
v_a_1985_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1967_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1967_);
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
else
{
lean_object* v_vs_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2028_; 
v_vs_1994_ = lean_ctor_get(v_n_1946_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_n_1946_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1996_ = v_n_1946_;
v_isShared_1997_ = v_isSharedCheck_2028_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_vs_1994_);
lean_dec(v_n_1946_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2028_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; size_t v_sz_2000_; size_t v___x_2001_; lean_object* v___x_2002_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v_b_1947_);
v_sz_2000_ = lean_array_size(v_vs_1994_);
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_vs_1994_, v_sz_2000_, v___x_2001_, v___x_1999_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec_ref(v_vs_1994_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2019_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2019_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2019_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_fst_2007_; 
v_fst_2007_ = lean_ctor_get(v_a_2003_, 0);
if (lean_obj_tag(v_fst_2007_) == 0)
{
lean_object* v_snd_2008_; lean_object* v___x_2010_; 
v_snd_2008_ = lean_ctor_get(v_a_2003_, 1);
lean_inc(v_snd_2008_);
lean_dec(v_a_2003_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v_snd_2008_);
v___x_2010_ = v___x_1996_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_snd_2008_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2010_);
v___x_2012_ = v___x_2005_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; 
lean_inc_ref(v_fst_2007_);
lean_dec(v_a_2003_);
lean_del_object(v___x_1996_);
v_val_2015_ = lean_ctor_get(v_fst_2007_, 0);
lean_inc(v_val_2015_);
lean_dec_ref(v_fst_2007_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_val_2015_);
v___x_2017_ = v___x_2005_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_del_object(v___x_1996_);
v_a_2020_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2002_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2002_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(lean_object* v_inh_2029_, lean_object* v_as_2030_, size_t v_sz_2031_, size_t v_i_2032_, lean_object* v_b_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_usize_dec_lt(v_i_2032_, v_sz_2031_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_b_2033_);
return v___x_2046_;
}
else
{
lean_object* v_snd_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2081_; 
v_snd_2047_ = lean_ctor_get(v_b_2033_, 1);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_b_2033_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v_b_2033_, 0);
lean_dec(v_unused_2082_);
v___x_2049_ = v_b_2033_;
v_isShared_2050_ = v_isSharedCheck_2081_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_snd_2047_);
lean_dec(v_b_2033_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2081_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_a_2051_; lean_object* v___x_2052_; 
v_a_2051_ = lean_array_uget_borrowed(v_as_2030_, v_i_2032_);
lean_inc(v_snd_2047_);
lean_inc(v_a_2051_);
v___x_2052_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_inh_2029_, v_a_2051_, v_snd_2047_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2072_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2072_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2072_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
if (lean_obj_tag(v_a_2053_) == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_a_2053_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2057_);
v___x_2059_ = v___x_2049_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_snd_2047_);
v___x_2059_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2059_);
v___x_2061_ = v___x_2055_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
lean_del_object(v___x_2055_);
lean_dec(v_snd_2047_);
v_a_2064_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v_a_2053_);
v___x_2065_ = lean_box(0);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v_a_2064_);
lean_ctor_set(v___x_2049_, 0, v___x_2065_);
v___x_2067_ = v___x_2049_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_a_2064_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
size_t v___x_2068_; size_t v___x_2069_; 
v___x_2068_ = ((size_t)1ULL);
v___x_2069_ = lean_usize_add(v_i_2032_, v___x_2068_);
v_i_2032_ = v___x_2069_;
v_b_2033_ = v___x_2067_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_del_object(v___x_2049_);
lean_dec(v_snd_2047_);
v_a_2073_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2052_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2052_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2___boxed(lean_object* v_inh_2083_, lean_object* v_as_2084_, lean_object* v_sz_2085_, lean_object* v_i_2086_, lean_object* v_b_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
size_t v_sz_boxed_2099_; size_t v_i_boxed_2100_; lean_object* v_res_2101_; 
v_sz_boxed_2099_ = lean_unbox_usize(v_sz_2085_);
lean_dec(v_sz_2085_);
v_i_boxed_2100_ = lean_unbox_usize(v_i_2086_);
lean_dec(v_i_2086_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_inh_2083_, v_as_2084_, v_sz_boxed_2099_, v_i_boxed_2100_, v_b_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v_as_2084_);
lean_dec(v_inh_2083_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1___boxed(lean_object* v_inh_2102_, lean_object* v_n_2103_, lean_object* v_b_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_inh_2102_, v_n_2103_, v_b_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec(v_inh_2102_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(lean_object* v_as_2117_, size_t v_sz_2118_, size_t v_i_2119_, lean_object* v_b_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_usize_dec_lt(v_i_2119_, v_sz_2118_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_b_2120_);
return v___x_2133_;
}
else
{
lean_object* v_snd_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2193_; 
v_snd_2134_ = lean_ctor_get(v_b_2120_, 1);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_b_2120_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; 
v_unused_2194_ = lean_ctor_get(v_b_2120_, 0);
lean_dec(v_unused_2194_);
v___x_2136_ = v_b_2120_;
v_isShared_2137_ = v_isSharedCheck_2193_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snd_2134_);
lean_dec(v_b_2120_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2193_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v_a_2140_; lean_object* v_a_2150_; 
v___x_2138_ = lean_box(0);
v_a_2150_ = lean_array_uget(v_as_2117_, v_i_2119_);
if (lean_obj_tag(v_a_2150_) == 1)
{
lean_object* v_val_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2192_; 
v_val_2151_ = lean_ctor_get(v_a_2150_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_a_2150_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2153_ = v_a_2150_;
v_isShared_2154_ = v_isSharedCheck_2192_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_val_2151_);
lean_dec(v_a_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2192_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_d_2155_; lean_object* v_p_2156_; lean_object* v___x_2157_; 
v_d_2155_ = lean_ctor_get(v_val_2151_, 0);
lean_inc(v_d_2155_);
v_p_2156_ = lean_ctor_get(v_val_2151_, 1);
lean_inc_ref(v_p_2156_);
lean_dec(v_val_2151_);
v___x_2157_ = l_Int_Linear_Poly_checkCnstrOf(v_p_2156_, v_snd_2134_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec_ref(v_p_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
lean_dec_ref(v___x_2157_);
v___x_2158_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2159_ = lean_int_dec_lt(v___x_2158_, v_d_2155_);
lean_dec(v_d_2155_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2161_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2160_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2175_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2175_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2175_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
if (lean_obj_tag(v_a_2162_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; 
lean_del_object(v___x_2136_);
v_a_2166_ = lean_ctor_get(v_a_2162_, 0);
lean_inc(v_a_2166_);
lean_dec_ref(v_a_2162_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v_a_2166_);
v___x_2168_ = v___x_2153_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2166_);
v___x_2168_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v_snd_2134_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2169_);
v___x_2171_ = v___x_2164_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_object* v_a_2174_; 
lean_del_object(v___x_2164_);
lean_del_object(v___x_2153_);
lean_dec(v_snd_2134_);
v_a_2174_ = lean_ctor_get(v_a_2162_, 0);
lean_inc(v_a_2174_);
lean_dec_ref(v_a_2162_);
v_a_2140_ = v_a_2174_;
goto v___jp_2139_;
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_del_object(v___x_2153_);
lean_del_object(v___x_2136_);
lean_dec(v_snd_2134_);
v_a_2176_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2161_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2161_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_del_object(v___x_2153_);
goto v___jp_2147_;
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_d_2155_);
lean_del_object(v___x_2153_);
lean_del_object(v___x_2136_);
lean_dec(v_snd_2134_);
v_a_2184_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2157_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2157_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
else
{
lean_dec(v_a_2150_);
goto v___jp_2147_;
}
v___jp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v_a_2140_);
lean_ctor_set(v___x_2136_, 0, v___x_2138_);
v___x_2142_ = v___x_2136_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_a_2140_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
size_t v___x_2143_; size_t v___x_2144_; 
v___x_2143_ = ((size_t)1ULL);
v___x_2144_ = lean_usize_add(v_i_2119_, v___x_2143_);
v_i_2119_ = v___x_2144_;
v_b_2120_ = v___x_2142_;
goto _start;
}
}
v___jp_2147_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = lean_nat_add(v_snd_2134_, v___x_2148_);
lean_dec(v_snd_2134_);
v_a_2140_ = v___x_2149_;
goto v___jp_2139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2195_, lean_object* v_sz_2196_, lean_object* v_i_2197_, lean_object* v_b_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
size_t v_sz_boxed_2210_; size_t v_i_boxed_2211_; lean_object* v_res_2212_; 
v_sz_boxed_2210_ = lean_unbox_usize(v_sz_2196_);
lean_dec(v_sz_2196_);
v_i_boxed_2211_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_res_2212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2195_, v_sz_boxed_2210_, v_i_boxed_2211_, v_b_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v_as_2195_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(lean_object* v_as_2213_, size_t v_sz_2214_, size_t v_i_2215_, lean_object* v_b_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_usize_dec_lt(v_i_2215_, v_sz_2214_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_b_2216_);
return v___x_2229_;
}
else
{
lean_object* v_snd_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2289_; 
v_snd_2230_ = lean_ctor_get(v_b_2216_, 1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_b_2216_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v_b_2216_, 0);
lean_dec(v_unused_2290_);
v___x_2232_ = v_b_2216_;
v_isShared_2233_ = v_isSharedCheck_2289_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_snd_2230_);
lean_dec(v_b_2216_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2289_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v_a_2236_; lean_object* v_a_2246_; 
v___x_2234_ = lean_box(0);
v_a_2246_ = lean_array_uget(v_as_2213_, v_i_2215_);
if (lean_obj_tag(v_a_2246_) == 1)
{
lean_object* v_val_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2288_; 
v_val_2247_ = lean_ctor_get(v_a_2246_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_a_2246_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2249_ = v_a_2246_;
v_isShared_2250_ = v_isSharedCheck_2288_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_val_2247_);
lean_dec(v_a_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2288_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_d_2251_; lean_object* v_p_2252_; lean_object* v___x_2253_; 
v_d_2251_ = lean_ctor_get(v_val_2247_, 0);
lean_inc(v_d_2251_);
v_p_2252_ = lean_ctor_get(v_val_2247_, 1);
lean_inc_ref(v_p_2252_);
lean_dec(v_val_2247_);
v___x_2253_ = l_Int_Linear_Poly_checkCnstrOf(v_p_2252_, v_snd_2230_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec_ref(v_p_2252_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
lean_dec_ref(v___x_2253_);
v___x_2254_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2255_ = lean_int_dec_lt(v___x_2254_, v_d_2251_);
lean_dec(v_d_2251_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2257_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2256_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2271_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2271_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2271_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
if (lean_obj_tag(v_a_2258_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; 
lean_del_object(v___x_2232_);
v_a_2262_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_a_2262_);
lean_dec_ref(v_a_2258_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v_a_2262_);
v___x_2264_ = v___x_2249_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2262_);
v___x_2264_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_snd_2230_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2265_);
v___x_2267_ = v___x_2260_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
else
{
lean_object* v_a_2270_; 
lean_del_object(v___x_2260_);
lean_del_object(v___x_2249_);
lean_dec(v_snd_2230_);
v_a_2270_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v_a_2258_);
v_a_2236_ = v_a_2270_;
goto v___jp_2235_;
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_del_object(v___x_2249_);
lean_del_object(v___x_2232_);
lean_dec(v_snd_2230_);
v_a_2272_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2257_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2257_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_del_object(v___x_2249_);
goto v___jp_2243_;
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_d_2251_);
lean_del_object(v___x_2249_);
lean_del_object(v___x_2232_);
lean_dec(v_snd_2230_);
v_a_2280_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2253_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2253_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
else
{
lean_dec(v_a_2246_);
goto v___jp_2243_;
}
v___jp_2235_:
{
lean_object* v___x_2238_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v_a_2236_);
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2238_ = v___x_2232_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_a_2236_);
v___x_2238_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
size_t v___x_2239_; size_t v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = ((size_t)1ULL);
v___x_2240_ = lean_usize_add(v_i_2215_, v___x_2239_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2213_, v_sz_2214_, v___x_2240_, v___x_2238_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
return v___x_2241_;
}
}
v___jp_2243_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_unsigned_to_nat(1u);
v___x_2245_ = lean_nat_add(v_snd_2230_, v___x_2244_);
lean_dec(v_snd_2230_);
v_a_2236_ = v___x_2245_;
goto v___jp_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2___boxed(lean_object* v_as_2291_, lean_object* v_sz_2292_, lean_object* v_i_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
size_t v_sz_boxed_2306_; size_t v_i_boxed_2307_; lean_object* v_res_2308_; 
v_sz_boxed_2306_ = lean_unbox_usize(v_sz_2292_);
lean_dec(v_sz_2292_);
v_i_boxed_2307_ = lean_unbox_usize(v_i_2293_);
lean_dec(v_i_2293_);
v_res_2308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_as_2291_, v_sz_boxed_2306_, v_i_boxed_2307_, v_b_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v_as_2291_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(lean_object* v_t_2309_, lean_object* v_init_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_root_2322_; lean_object* v_tail_2323_; lean_object* v___x_2324_; 
v_root_2322_ = lean_ctor_get(v_t_2309_, 0);
lean_inc_ref(v_root_2322_);
v_tail_2323_ = lean_ctor_get(v_t_2309_, 1);
lean_inc_ref(v_tail_2323_);
lean_dec_ref(v_t_2309_);
lean_inc(v_init_2310_);
v___x_2324_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2310_, v_root_2322_, v_init_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v_init_2310_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2361_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2361_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2361_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
if (lean_obj_tag(v_a_2325_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; 
lean_dec_ref(v_tail_2323_);
v_a_2329_ = lean_ctor_get(v_a_2325_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v_a_2325_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v_a_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; size_t v_sz_2336_; size_t v___x_2337_; lean_object* v___x_2338_; 
lean_del_object(v___x_2327_);
v_a_2333_ = lean_ctor_get(v_a_2325_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v_a_2325_);
v___x_2334_ = lean_box(0);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v_a_2333_);
v_sz_2336_ = lean_array_size(v_tail_2323_);
v___x_2337_ = ((size_t)0ULL);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_tail_2323_, v_sz_2336_, v___x_2337_, v___x_2335_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec_ref(v_tail_2323_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2352_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2352_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2352_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_fst_2343_; 
v_fst_2343_ = lean_ctor_get(v_a_2339_, 0);
if (lean_obj_tag(v_fst_2343_) == 0)
{
lean_object* v_snd_2344_; lean_object* v___x_2346_; 
v_snd_2344_ = lean_ctor_get(v_a_2339_, 1);
lean_inc(v_snd_2344_);
lean_dec(v_a_2339_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v_snd_2344_);
v___x_2346_ = v___x_2341_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_snd_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
else
{
lean_object* v_val_2348_; lean_object* v___x_2350_; 
lean_inc_ref(v_fst_2343_);
lean_dec(v_a_2339_);
v_val_2348_ = lean_ctor_get(v_fst_2343_, 0);
lean_inc(v_val_2348_);
lean_dec_ref(v_fst_2343_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v_val_2348_);
v___x_2350_ = v___x_2341_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_val_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2338_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2338_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_tail_2323_);
v_a_2362_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2324_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2324_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1___boxed(lean_object* v_t_2370_, lean_object* v_init_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_t_2370_, v_init_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
return v_res_2383_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2385_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0));
v___x_2386_ = lean_unsigned_to_nat(2u);
v___x_2387_ = lean_unsigned_to_nat(65u);
v___x_2388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_2389_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_2390_ = l_mkPanicMessageWithDecl(v___x_2389_, v___x_2388_, v___x_2387_, v___x_2386_, v___x_2385_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2391_, v_a_2399_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v_vars_2404_; lean_object* v_dvds_2405_; lean_object* v_size_2406_; lean_object* v_size_2407_; uint8_t v___x_2408_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2402_);
v_vars_2404_ = lean_ctor_get(v_a_2403_, 0);
lean_inc_ref(v_vars_2404_);
v_dvds_2405_ = lean_ctor_get(v_a_2403_, 6);
lean_inc_ref(v_dvds_2405_);
lean_dec(v_a_2403_);
v_size_2406_ = lean_ctor_get(v_vars_2404_, 2);
lean_inc(v_size_2406_);
lean_dec_ref(v_vars_2404_);
v_size_2407_ = lean_ctor_get(v_dvds_2405_, 2);
v___x_2408_ = lean_nat_dec_eq(v_size_2406_, v_size_2407_);
lean_dec(v_size_2406_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec_ref(v_dvds_2405_);
v___x_2409_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1);
v___x_2410_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_2409_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_dvds_2405_, v___x_2411_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2420_; 
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v___x_2412_, 0);
lean_dec(v_unused_2421_);
v___x_2414_ = v___x_2412_;
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
else
{
lean_dec(v___x_2412_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = lean_box(0);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2418_ = v___x_2414_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_a_2422_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2412_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2412_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v_a_2430_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2402_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2402_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___boxed(lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec(v_a_2438_);
return v_res_2449_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2451_ = ((lean_object*)(l_Int_Linear_Poly_checkCnstrOf___closed__3));
v___x_2452_ = lean_unsigned_to_nat(6u);
v___x_2453_ = lean_unsigned_to_nat(81u);
v___x_2454_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2455_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_2456_ = l_mkPanicMessageWithDecl(v___x_2455_, v___x_2454_, v___x_2453_, v___x_2452_, v___x_2451_);
return v___x_2456_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2458_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2));
v___x_2459_ = lean_unsigned_to_nat(6u);
v___x_2460_ = lean_unsigned_to_nat(79u);
v___x_2461_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2462_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_2463_ = l_mkPanicMessageWithDecl(v___x_2462_, v___x_2461_, v___x_2460_, v___x_2459_, v___x_2458_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(lean_object* v_vars_2464_, lean_object* v_x_2465_, lean_object* v_____s_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v_size_2485_; uint8_t v___x_2486_; 
v_fst_2483_ = lean_ctor_get(v_x_2465_, 0);
v_snd_2484_ = lean_ctor_get(v_x_2465_, 1);
v_size_2485_ = lean_ctor_get(v_vars_2464_, 2);
v___x_2486_ = lean_nat_dec_lt(v_snd_2484_, v_size_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_dec_ref(v_vars_2464_);
v___x_2487_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1);
v___x_2488_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_2487_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_dec_ref(v___x_2488_);
goto v___jp_2478_;
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2497_ = l_Lean_instInhabitedExpr;
v___x_2498_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2497_, v_vars_2464_, v_snd_2484_);
v___x_2499_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2483_, v___x_2498_);
lean_dec(v___x_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3);
v___x_2501_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2500_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
return v___x_2501_;
}
else
{
goto v___jp_2478_;
}
}
v___jp_2478_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = lean_nat_add(v_____s_2466_, v___x_2479_);
v___x_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(lean_object* v_vars_2502_, lean_object* v_x_2503_, lean_object* v_____s_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(v_vars_2502_, v_x_2503_, v_____s_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec(v_____s_2504_);
lean_dec_ref(v_x_2503_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2517_, lean_object* v_keys_2518_, lean_object* v_vals_2519_, lean_object* v_i_2520_, lean_object* v_acc_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = lean_array_get_size(v_keys_2518_);
v___x_2534_ = lean_nat_dec_lt(v_i_2520_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec(v_i_2520_);
lean_dec_ref(v_f_2517_);
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_acc_2521_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
else
{
lean_object* v_k_2537_; lean_object* v_v_2538_; lean_object* v___x_2539_; 
v_k_2537_ = lean_array_fget_borrowed(v_keys_2518_, v_i_2520_);
v_v_2538_ = lean_array_fget_borrowed(v_vals_2519_, v_i_2520_);
lean_inc_ref(v_f_2517_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc(v___y_2525_);
lean_inc_ref(v___y_2524_);
lean_inc(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc(v_v_2538_);
lean_inc(v_k_2537_);
v___x_2539_ = lean_apply_14(v_f_2517_, v_acc_2521_, v_k_2537_, v_v_2538_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, lean_box(0));
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
if (lean_obj_tag(v_a_2540_) == 0)
{
lean_dec_ref(v_a_2540_);
lean_dec(v_i_2520_);
lean_dec_ref(v_f_2517_);
return v___x_2539_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec_ref(v___x_2539_);
v_a_2541_ = lean_ctor_get(v_a_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v_a_2540_);
v___x_2542_ = lean_unsigned_to_nat(1u);
v___x_2543_ = lean_nat_add(v_i_2520_, v___x_2542_);
lean_dec(v_i_2520_);
v_i_2520_ = v___x_2543_;
v_acc_2521_ = v_a_2541_;
goto _start;
}
}
else
{
lean_dec(v_i_2520_);
lean_dec_ref(v_f_2517_);
return v___x_2539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2545_, lean_object* v_keys_2546_, lean_object* v_vals_2547_, lean_object* v_i_2548_, lean_object* v_acc_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2545_, v_keys_2546_, v_vals_2547_, v_i_2548_, v_acc_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v_vals_2547_);
lean_dec_ref(v_keys_2546_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
if (lean_obj_tag(v_x_2563_) == 0)
{
lean_object* v_es_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2598_; 
v_es_2576_ = lean_ctor_get(v_x_2563_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_x_2563_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2578_ = v_x_2563_;
v_isShared_2579_ = v_isSharedCheck_2598_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_es_2576_);
lean_dec(v_x_2563_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2598_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = lean_array_get_size(v_es_2576_);
v___x_2582_ = lean_nat_dec_lt(v___x_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2584_; 
lean_dec_ref(v_es_2576_);
lean_dec_ref(v_f_2562_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 1);
lean_ctor_set(v___x_2578_, 0, v_x_2564_);
v___x_2584_ = v___x_2578_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_x_2564_);
v___x_2584_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
}
else
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_nat_dec_le(v___x_2581_, v___x_2581_);
if (v___x_2587_ == 0)
{
if (v___x_2582_ == 0)
{
lean_object* v___x_2589_; 
lean_dec_ref(v_es_2576_);
lean_dec_ref(v_f_2562_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 1);
lean_ctor_set(v___x_2578_, 0, v_x_2564_);
v___x_2589_ = v___x_2578_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_x_2564_);
v___x_2589_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; 
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
lean_del_object(v___x_2578_);
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2581_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2562_, v_es_2576_, v___x_2592_, v___x_2593_, v_x_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec_ref(v_es_2576_);
return v___x_2594_;
}
}
else
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; 
lean_del_object(v___x_2578_);
v___x_2595_ = ((size_t)0ULL);
v___x_2596_ = lean_usize_of_nat(v___x_2581_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2562_, v_es_2576_, v___x_2595_, v___x_2596_, v_x_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec_ref(v_es_2576_);
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_ks_2599_; lean_object* v_vs_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_ks_2599_ = lean_ctor_get(v_x_2563_, 0);
lean_inc_ref(v_ks_2599_);
v_vs_2600_ = lean_ctor_get(v_x_2563_, 1);
lean_inc_ref(v_vs_2600_);
lean_dec_ref(v_x_2563_);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2562_, v_ks_2599_, v_vs_2600_, v___x_2601_, v_x_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec_ref(v_vs_2600_);
lean_dec_ref(v_ks_2599_);
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2603_, lean_object* v_as_2604_, size_t v_i_2605_, size_t v_stop_2606_, lean_object* v_b_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_a_2620_; lean_object* v___y_2625_; uint8_t v___x_2628_; 
v___x_2628_ = lean_usize_dec_eq(v_i_2605_, v_stop_2606_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_array_uget_borrowed(v_as_2604_, v_i_2605_);
switch(lean_obj_tag(v___x_2629_))
{
case 0:
{
lean_object* v_key_2630_; lean_object* v_val_2631_; lean_object* v___x_2632_; 
v_key_2630_ = lean_ctor_get(v___x_2629_, 0);
v_val_2631_ = lean_ctor_get(v___x_2629_, 1);
lean_inc_ref(v_f_2603_);
lean_inc(v___y_2617_);
lean_inc_ref(v___y_2616_);
lean_inc(v___y_2615_);
lean_inc_ref(v___y_2614_);
lean_inc(v___y_2613_);
lean_inc_ref(v___y_2612_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2609_);
lean_inc(v___y_2608_);
lean_inc(v_val_2631_);
lean_inc(v_key_2630_);
v___x_2632_ = lean_apply_14(v_f_2603_, v_b_2607_, v_key_2630_, v_val_2631_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, lean_box(0));
v___y_2625_ = v___x_2632_;
goto v___jp_2624_;
}
case 1:
{
lean_object* v_node_2633_; lean_object* v___x_2634_; 
v_node_2633_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_node_2633_);
lean_inc_ref(v_f_2603_);
v___x_2634_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2603_, v_node_2633_, v_b_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
v___y_2625_ = v___x_2634_;
goto v___jp_2624_;
}
default: 
{
v_a_2620_ = v_b_2607_;
goto v___jp_2619_;
}
}
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_dec_ref(v_f_2603_);
v___x_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_b_2607_);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
v___jp_2619_:
{
size_t v___x_2621_; size_t v___x_2622_; 
v___x_2621_ = ((size_t)1ULL);
v___x_2622_ = lean_usize_add(v_i_2605_, v___x_2621_);
v_i_2605_ = v___x_2622_;
v_b_2607_ = v_a_2620_;
goto _start;
}
v___jp_2624_:
{
if (lean_obj_tag(v___y_2625_) == 0)
{
lean_object* v_a_2626_; 
v_a_2626_ = lean_ctor_get(v___y_2625_, 0);
if (lean_obj_tag(v_a_2626_) == 0)
{
lean_dec_ref(v_f_2603_);
return v___y_2625_;
}
else
{
lean_object* v_a_2627_; 
lean_inc_ref(v_a_2626_);
lean_dec_ref(v___y_2625_);
v_a_2627_ = lean_ctor_get(v_a_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref(v_a_2626_);
v_a_2620_ = v_a_2627_;
goto v___jp_2619_;
}
}
else
{
lean_dec_ref(v_f_2603_);
return v___y_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2637_, lean_object* v_as_2638_, lean_object* v_i_2639_, lean_object* v_stop_2640_, lean_object* v_b_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
size_t v_i_boxed_2653_; size_t v_stop_boxed_2654_; lean_object* v_res_2655_; 
v_i_boxed_2653_ = lean_unbox_usize(v_i_2639_);
lean_dec(v_i_2639_);
v_stop_boxed_2654_ = lean_unbox_usize(v_stop_2640_);
lean_dec(v_stop_2640_);
v_res_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2637_, v_as_2638_, v_i_boxed_2653_, v_stop_boxed_2654_, v_b_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v_as_2638_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2656_, v_x_2657_, v_x_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec(v___y_2659_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(lean_object* v_f_2671_, lean_object* v_s_2672_, lean_object* v_a_2673_, lean_object* v_b_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v_a_2673_);
lean_ctor_set(v___x_2686_, 1, v_b_2674_);
lean_inc(v___y_2684_);
lean_inc_ref(v___y_2683_);
lean_inc(v___y_2682_);
lean_inc_ref(v___y_2681_);
lean_inc(v___y_2680_);
lean_inc_ref(v___y_2679_);
lean_inc(v___y_2678_);
lean_inc_ref(v___y_2677_);
lean_inc(v___y_2676_);
lean_inc(v___y_2675_);
v___x_2687_ = lean_apply_13(v_f_2671_, v___x_2686_, v_s_2672_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, lean_box(0));
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2714_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2714_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2714_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
if (lean_obj_tag(v_a_2688_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2702_; 
v_a_2692_ = lean_ctor_get(v_a_2688_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_a_2688_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2694_ = v_a_2688_;
v_isShared_2695_ = v_isSharedCheck_2702_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v_a_2688_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2702_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2699_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2697_);
v___x_2699_ = v___x_2690_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2713_; 
v_a_2703_ = lean_ctor_get(v_a_2688_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_a_2688_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2705_ = v_a_2688_;
v_isShared_2706_ = v_isSharedCheck_2713_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v_a_2688_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2713_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2710_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2708_);
v___x_2710_ = v___x_2690_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
v_a_2715_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2687_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2687_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed(lean_object* v_f_2723_, lean_object* v_s_2724_, lean_object* v_a_2725_, lean_object* v_b_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(v_f_2723_, v_s_2724_, v_a_2725_, v_b_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v___y_2727_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(lean_object* v_map_2739_, lean_object* v_init_2740_, lean_object* v_f_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___f_2753_; lean_object* v___x_2754_; 
v___f_2753_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed), 15, 1);
lean_closure_set(v___f_2753_, 0, v_f_2741_);
v___x_2754_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v___f_2753_, v_map_2739_, v_init_2740_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2763_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v_a_2759_; lean_object* v___x_2761_; 
v_a_2759_ = lean_ctor_get(v_a_2755_, 0);
lean_inc(v_a_2759_);
lean_dec(v_a_2755_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v_a_2759_);
v___x_2761_ = v___x_2757_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v_a_2764_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2754_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2754_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___boxed(lean_object* v_map_2772_, lean_object* v_init_2773_, lean_object* v_f_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2772_, v_init_2773_, v_f_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec(v___y_2775_);
return v_res_2786_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2788_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0));
v___x_2789_ = lean_unsigned_to_nat(2u);
v___x_2790_ = lean_unsigned_to_nat(83u);
v___x_2791_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2792_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_2793_ = l_mkPanicMessageWithDecl(v___x_2792_, v___x_2791_, v___x_2790_, v___x_2789_, v___x_2788_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars(lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2794_, v_a_2802_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v_vars_2807_; lean_object* v_varMap_2808_; lean_object* v___f_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
v_vars_2807_ = lean_ctor_get(v_a_2806_, 0);
lean_inc_ref(v_vars_2807_);
v_varMap_2808_ = lean_ctor_get(v_a_2806_, 1);
lean_inc_ref(v_varMap_2808_);
lean_dec(v_a_2806_);
lean_inc_ref(v_vars_2807_);
v___f_2809_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2809_, 0, v_vars_2807_);
v___x_2810_ = lean_unsigned_to_nat(0u);
v___x_2811_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_varMap_2808_, v___x_2810_, v___f_2809_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2824_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2824_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2824_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_size_2816_; uint8_t v___x_2817_; 
v_size_2816_ = lean_ctor_get(v_vars_2807_, 2);
lean_inc(v_size_2816_);
lean_dec_ref(v_vars_2807_);
v___x_2817_ = lean_nat_dec_eq(v_size_2816_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec(v_size_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_del_object(v___x_2814_);
v___x_2818_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1);
v___x_2819_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_2818_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2820_ = lean_box(0);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2820_);
v___x_2822_ = v___x_2814_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec_ref(v_vars_2807_);
v_a_2825_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2811_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2811_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
v_a_2833_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2805_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2805_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___boxed(lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec(v_a_2841_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(lean_object* v_00_u03c3_2853_, lean_object* v_00_u03b2_2854_, lean_object* v_map_2855_, lean_object* v_init_2856_, lean_object* v_f_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2855_, v_init_2856_, v_f_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___boxed(lean_object* v_00_u03c3_2870_, lean_object* v_00_u03b2_2871_, lean_object* v_map_2872_, lean_object* v_init_2873_, lean_object* v_f_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(v_00_u03c3_2870_, v_00_u03b2_2871_, v_map_2872_, v_init_2873_, v_f_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2875_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(lean_object* v_map_2887_, lean_object* v_f_2888_, lean_object* v_init_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2888_, v_map_2887_, v_init_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_map_2902_, lean_object* v_f_2903_, lean_object* v_init_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(v_map_2902_, v_f_2903_, v_init_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(lean_object* v_00_u03c3_2917_, lean_object* v_00_u03c3_2918_, lean_object* v_00_u03b2_2919_, lean_object* v_map_2920_, lean_object* v_f_2921_, lean_object* v_init_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2921_, v_map_2920_, v_init_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_2935_ = _args[0];
lean_object* v_00_u03c3_2936_ = _args[1];
lean_object* v_00_u03b2_2937_ = _args[2];
lean_object* v_map_2938_ = _args[3];
lean_object* v_f_2939_ = _args[4];
lean_object* v_init_2940_ = _args[5];
lean_object* v___y_2941_ = _args[6];
lean_object* v___y_2942_ = _args[7];
lean_object* v___y_2943_ = _args[8];
lean_object* v___y_2944_ = _args[9];
lean_object* v___y_2945_ = _args[10];
lean_object* v___y_2946_ = _args[11];
lean_object* v___y_2947_ = _args[12];
lean_object* v___y_2948_ = _args[13];
lean_object* v___y_2949_ = _args[14];
lean_object* v___y_2950_ = _args[15];
lean_object* v___y_2951_ = _args[16];
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(v_00_u03c3_2935_, v_00_u03c3_2936_, v_00_u03b2_2937_, v_map_2938_, v_f_2939_, v_init_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2953_, lean_object* v_00_u03c3_2954_, lean_object* v_00_u03b1_2955_, lean_object* v_00_u03b2_2956_, lean_object* v_f_2957_, lean_object* v_x_2958_, lean_object* v_x_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2957_, v_x_2958_, v_x_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_2972_ = _args[0];
lean_object* v_00_u03c3_2973_ = _args[1];
lean_object* v_00_u03b1_2974_ = _args[2];
lean_object* v_00_u03b2_2975_ = _args[3];
lean_object* v_f_2976_ = _args[4];
lean_object* v_x_2977_ = _args[5];
lean_object* v_x_2978_ = _args[6];
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
lean_object* v___y_2989_ = _args[17];
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(v_00_u03c3_2972_, v_00_u03c3_2973_, v_00_u03b1_2974_, v_00_u03b2_2975_, v_f_2976_, v_x_2977_, v_x_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v___y_2979_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2991_, lean_object* v_00_u03b2_2992_, lean_object* v_00_u03c3_2993_, lean_object* v_00_u03c3_2994_, lean_object* v_f_2995_, lean_object* v_as_2996_, size_t v_i_2997_, size_t v_stop_2998_, lean_object* v_b_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2995_, v_as_2996_, v_i_2997_, v_stop_2998_, v_b_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03b1_3012_ = _args[0];
lean_object* v_00_u03b2_3013_ = _args[1];
lean_object* v_00_u03c3_3014_ = _args[2];
lean_object* v_00_u03c3_3015_ = _args[3];
lean_object* v_f_3016_ = _args[4];
lean_object* v_as_3017_ = _args[5];
lean_object* v_i_3018_ = _args[6];
lean_object* v_stop_3019_ = _args[7];
lean_object* v_b_3020_ = _args[8];
lean_object* v___y_3021_ = _args[9];
lean_object* v___y_3022_ = _args[10];
lean_object* v___y_3023_ = _args[11];
lean_object* v___y_3024_ = _args[12];
lean_object* v___y_3025_ = _args[13];
lean_object* v___y_3026_ = _args[14];
lean_object* v___y_3027_ = _args[15];
lean_object* v___y_3028_ = _args[16];
lean_object* v___y_3029_ = _args[17];
lean_object* v___y_3030_ = _args[18];
lean_object* v___y_3031_ = _args[19];
_start:
{
size_t v_i_boxed_3032_; size_t v_stop_boxed_3033_; lean_object* v_res_3034_; 
v_i_boxed_3032_ = lean_unbox_usize(v_i_3018_);
lean_dec(v_i_3018_);
v_stop_boxed_3033_ = lean_unbox_usize(v_stop_3019_);
lean_dec(v_stop_3019_);
v_res_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3012_, v_00_u03b2_3013_, v_00_u03c3_3014_, v_00_u03c3_3015_, v_f_3016_, v_as_3017_, v_i_boxed_3032_, v_stop_boxed_3033_, v_b_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v_as_3017_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3035_, lean_object* v_00_u03c3_3036_, lean_object* v_00_u03b1_3037_, lean_object* v_00_u03b2_3038_, lean_object* v_f_3039_, lean_object* v_keys_3040_, lean_object* v_vals_3041_, lean_object* v_heq_3042_, lean_object* v_i_3043_, lean_object* v_acc_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3039_, v_keys_3040_, v_vals_3041_, v_i_3043_, v_acc_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_3057_ = _args[0];
lean_object* v_00_u03c3_3058_ = _args[1];
lean_object* v_00_u03b1_3059_ = _args[2];
lean_object* v_00_u03b2_3060_ = _args[3];
lean_object* v_f_3061_ = _args[4];
lean_object* v_keys_3062_ = _args[5];
lean_object* v_vals_3063_ = _args[6];
lean_object* v_heq_3064_ = _args[7];
lean_object* v_i_3065_ = _args[8];
lean_object* v_acc_3066_ = _args[9];
lean_object* v___y_3067_ = _args[10];
lean_object* v___y_3068_ = _args[11];
lean_object* v___y_3069_ = _args[12];
lean_object* v___y_3070_ = _args[13];
lean_object* v___y_3071_ = _args[14];
lean_object* v___y_3072_ = _args[15];
lean_object* v___y_3073_ = _args[16];
lean_object* v___y_3074_ = _args[17];
lean_object* v___y_3075_ = _args[18];
lean_object* v___y_3076_ = _args[19];
lean_object* v___y_3077_ = _args[20];
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3057_, v_00_u03c3_3058_, v_00_u03b1_3059_, v_00_u03b2_3060_, v_f_3061_, v_keys_3062_, v_vals_3063_, v_heq_3064_, v_i_3065_, v_acc_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v_vals_3063_);
lean_dec_ref(v_keys_3062_);
return v_res_3078_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(lean_object* v_a_3079_, lean_object* v_x_3080_){
_start:
{
if (lean_obj_tag(v_x_3080_) == 0)
{
uint8_t v___x_3081_; 
v___x_3081_ = 0;
return v___x_3081_;
}
else
{
lean_object* v_head_3082_; lean_object* v_tail_3083_; uint8_t v___x_3084_; 
v_head_3082_ = lean_ctor_get(v_x_3080_, 0);
v_tail_3083_ = lean_ctor_get(v_x_3080_, 1);
v___x_3084_ = lean_nat_dec_eq(v_a_3079_, v_head_3082_);
if (v___x_3084_ == 0)
{
v_x_3080_ = v_tail_3083_;
goto _start;
}
else
{
return v___x_3084_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0___boxed(lean_object* v_a_3086_, lean_object* v_x_3087_){
_start:
{
uint8_t v_res_3088_; lean_object* v_r_3089_; 
v_res_3088_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_a_3086_, v_x_3087_);
lean_dec(v_x_3087_);
lean_dec(v_a_3086_);
v_r_3089_ = lean_box(v_res_3088_);
return v_r_3089_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_3093_ = lean_unsigned_to_nat(6u);
v___x_3094_ = lean_unsigned_to_nat(94u);
v___x_3095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3096_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3097_ = l_mkPanicMessageWithDecl(v___x_3096_, v___x_3095_, v___x_3094_, v___x_3093_, v___x_3092_);
return v___x_3097_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3));
v___x_3100_ = lean_unsigned_to_nat(6u);
v___x_3101_ = lean_unsigned_to_nat(91u);
v___x_3102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3103_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3104_ = l_mkPanicMessageWithDecl(v___x_3103_, v___x_3102_, v___x_3101_, v___x_3100_, v___x_3099_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5));
v___x_3107_ = lean_unsigned_to_nat(6u);
v___x_3108_ = lean_unsigned_to_nat(92u);
v___x_3109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3110_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3111_ = l_mkPanicMessageWithDecl(v___x_3110_, v___x_3109_, v___x_3108_, v___x_3107_, v___x_3106_);
return v___x_3111_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7));
v___x_3114_ = lean_unsigned_to_nat(6u);
v___x_3115_ = lean_unsigned_to_nat(93u);
v___x_3116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3117_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3118_ = l_mkPanicMessageWithDecl(v___x_3117_, v___x_3116_, v___x_3115_, v___x_3114_, v___x_3113_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(lean_object* v_a_3119_, lean_object* v_as_3120_, size_t v_sz_3121_, size_t v_i_3122_, lean_object* v_b_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_usize_dec_lt(v_i_3122_, v_sz_3121_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_b_3123_);
return v___x_3136_;
}
else
{
lean_object* v_snd_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3193_; 
v_snd_3137_ = lean_ctor_get(v_b_3123_, 1);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_b_3123_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v_b_3123_, 0);
lean_dec(v_unused_3194_);
v___x_3139_ = v_b_3123_;
v_isShared_3140_ = v_isSharedCheck_3193_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_snd_3137_);
lean_dec(v_b_3123_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3193_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v_a_3143_; lean_object* v___y_3154_; lean_object* v_a_3177_; 
v___x_3141_ = lean_box(0);
v_a_3177_ = lean_array_uget_borrowed(v_as_3120_, v_i_3122_);
if (lean_obj_tag(v_a_3177_) == 1)
{
lean_object* v_val_3178_; lean_object* v_p_3179_; uint8_t v___x_3180_; 
v_val_3178_ = lean_ctor_get(v_a_3177_, 0);
v_p_3179_ = lean_ctor_get(v_val_3178_, 0);
v___x_3180_ = l_Int_Linear_Poly_isSorted(v_p_3179_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3182_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3181_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
v___y_3154_ = v___x_3182_;
goto v___jp_3153_;
}
else
{
uint8_t v___x_3183_; 
v___x_3183_ = l_Int_Linear_Poly_checkCoeffs(v_p_3179_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3185_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3184_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
v___y_3154_ = v___x_3185_;
goto v___jp_3153_;
}
else
{
lean_object* v_elimStack_3186_; uint8_t v___x_3187_; 
v_elimStack_3186_ = lean_ctor_get(v_a_3119_, 11);
v___x_3187_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3137_, v_elimStack_3186_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3189_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3188_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
v___y_3154_ = v___x_3189_;
goto v___jp_3153_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v___x_3190_ = l_Int_Linear_Poly_coeff(v_p_3179_, v_snd_3137_);
v___x_3191_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_3192_ = lean_int_dec_eq(v___x_3190_, v___x_3191_);
lean_dec(v___x_3190_);
if (v___x_3192_ == 0)
{
if (v___x_3187_ == 0)
{
goto v___jp_3174_;
}
else
{
goto v___jp_3150_;
}
}
else
{
goto v___jp_3174_;
}
}
}
}
}
else
{
goto v___jp_3150_;
}
v___jp_3142_:
{
lean_object* v___x_3145_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 1, v_a_3143_);
lean_ctor_set(v___x_3139_, 0, v___x_3141_);
v___x_3145_ = v___x_3139_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_a_3143_);
v___x_3145_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
size_t v___x_3146_; size_t v___x_3147_; 
v___x_3146_ = ((size_t)1ULL);
v___x_3147_ = lean_usize_add(v_i_3122_, v___x_3146_);
v_i_3122_ = v___x_3147_;
v_b_3123_ = v___x_3145_;
goto _start;
}
}
v___jp_3150_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_nat_add(v_snd_3137_, v___x_3151_);
lean_dec(v_snd_3137_);
v_a_3143_ = v___x_3152_;
goto v___jp_3142_;
}
v___jp_3153_:
{
if (lean_obj_tag(v___y_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3165_; 
v_a_3155_ = lean_ctor_get(v___y_3154_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___y_3154_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3157_ = v___y_3154_;
v_isShared_3158_ = v_isSharedCheck_3165_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___y_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3165_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
if (lean_obj_tag(v_a_3155_) == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
lean_del_object(v___x_3139_);
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_a_3155_);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v_snd_3137_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3160_);
v___x_3162_ = v___x_3157_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
else
{
lean_object* v_a_3164_; 
lean_del_object(v___x_3157_);
lean_dec(v_snd_3137_);
v_a_3164_ = lean_ctor_get(v_a_3155_, 0);
lean_inc(v_a_3164_);
lean_dec_ref(v_a_3155_);
v_a_3143_ = v_a_3164_;
goto v___jp_3142_;
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_del_object(v___x_3139_);
lean_dec(v_snd_3137_);
v_a_3166_ = lean_ctor_get(v___y_3154_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___y_3154_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___y_3154_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___y_3154_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
v___jp_3174_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3176_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3175_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
v___y_3154_ = v___x_3176_;
goto v___jp_3153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_a_3195_, lean_object* v_as_3196_, lean_object* v_sz_3197_, lean_object* v_i_3198_, lean_object* v_b_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
size_t v_sz_boxed_3211_; size_t v_i_boxed_3212_; lean_object* v_res_3213_; 
v_sz_boxed_3211_ = lean_unbox_usize(v_sz_3197_);
lean_dec(v_sz_3197_);
v_i_boxed_3212_ = lean_unbox_usize(v_i_3198_);
lean_dec(v_i_3198_);
v_res_3213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3195_, v_as_3196_, v_sz_boxed_3211_, v_i_boxed_3212_, v_b_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v_as_3196_);
lean_dec_ref(v_a_3195_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(lean_object* v_a_3214_, lean_object* v_as_3215_, size_t v_sz_3216_, size_t v_i_3217_, lean_object* v_b_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
uint8_t v___x_3230_; 
v___x_3230_ = lean_usize_dec_lt(v_i_3217_, v_sz_3216_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_b_3218_);
return v___x_3231_;
}
else
{
lean_object* v_snd_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3288_; 
v_snd_3232_ = lean_ctor_get(v_b_3218_, 1);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_b_3218_);
if (v_isSharedCheck_3288_ == 0)
{
lean_object* v_unused_3289_; 
v_unused_3289_ = lean_ctor_get(v_b_3218_, 0);
lean_dec(v_unused_3289_);
v___x_3234_ = v_b_3218_;
v_isShared_3235_ = v_isSharedCheck_3288_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_snd_3232_);
lean_dec(v_b_3218_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3288_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v_a_3238_; lean_object* v___y_3249_; lean_object* v_a_3272_; 
v___x_3236_ = lean_box(0);
v_a_3272_ = lean_array_uget_borrowed(v_as_3215_, v_i_3217_);
if (lean_obj_tag(v_a_3272_) == 1)
{
lean_object* v_val_3273_; lean_object* v_p_3274_; uint8_t v___x_3275_; 
v_val_3273_ = lean_ctor_get(v_a_3272_, 0);
v_p_3274_ = lean_ctor_get(v_val_3273_, 0);
v___x_3275_ = l_Int_Linear_Poly_isSorted(v_p_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3277_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3276_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
v___y_3249_ = v___x_3277_;
goto v___jp_3248_;
}
else
{
uint8_t v___x_3278_; 
v___x_3278_ = l_Int_Linear_Poly_checkCoeffs(v_p_3274_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3280_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3279_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
v___y_3249_ = v___x_3280_;
goto v___jp_3248_;
}
else
{
lean_object* v_elimStack_3281_; uint8_t v___x_3282_; 
v_elimStack_3281_ = lean_ctor_get(v_a_3214_, 11);
v___x_3282_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3232_, v_elimStack_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3284_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3283_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
v___y_3249_ = v___x_3284_;
goto v___jp_3248_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3285_ = l_Int_Linear_Poly_coeff(v_p_3274_, v_snd_3232_);
v___x_3286_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_3287_ = lean_int_dec_eq(v___x_3285_, v___x_3286_);
lean_dec(v___x_3285_);
if (v___x_3287_ == 0)
{
if (v___x_3282_ == 0)
{
goto v___jp_3269_;
}
else
{
goto v___jp_3245_;
}
}
else
{
goto v___jp_3269_;
}
}
}
}
}
else
{
goto v___jp_3245_;
}
v___jp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 1, v_a_3238_);
lean_ctor_set(v___x_3234_, 0, v___x_3236_);
v___x_3240_ = v___x_3234_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_a_3238_);
v___x_3240_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
size_t v___x_3241_; size_t v___x_3242_; lean_object* v___x_3243_; 
v___x_3241_ = ((size_t)1ULL);
v___x_3242_ = lean_usize_add(v_i_3217_, v___x_3241_);
v___x_3243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3214_, v_as_3215_, v_sz_3216_, v___x_3242_, v___x_3240_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
return v___x_3243_;
}
}
v___jp_3245_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = lean_unsigned_to_nat(1u);
v___x_3247_ = lean_nat_add(v_snd_3232_, v___x_3246_);
lean_dec(v_snd_3232_);
v_a_3238_ = v___x_3247_;
goto v___jp_3237_;
}
v___jp_3248_:
{
if (lean_obj_tag(v___y_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3260_; 
v_a_3250_ = lean_ctor_get(v___y_3249_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___y_3249_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3252_ = v___y_3249_;
v_isShared_3253_ = v_isSharedCheck_3260_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___y_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3260_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
if (lean_obj_tag(v_a_3250_) == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
lean_del_object(v___x_3234_);
v___x_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_a_3250_);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v_snd_3232_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3255_);
v___x_3257_ = v___x_3252_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
else
{
lean_object* v_a_3259_; 
lean_del_object(v___x_3252_);
lean_dec(v_snd_3232_);
v_a_3259_ = lean_ctor_get(v_a_3250_, 0);
lean_inc(v_a_3259_);
lean_dec_ref(v_a_3250_);
v_a_3238_ = v_a_3259_;
goto v___jp_3237_;
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_del_object(v___x_3234_);
lean_dec(v_snd_3232_);
v_a_3261_ = lean_ctor_get(v___y_3249_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___y_3249_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___y_3249_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___y_3249_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
v___jp_3269_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3271_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3270_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
v___y_3249_ = v___x_3271_;
goto v___jp_3248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3___boxed(lean_object* v_a_3290_, lean_object* v_as_3291_, lean_object* v_sz_3292_, lean_object* v_i_3293_, lean_object* v_b_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
size_t v_sz_boxed_3306_; size_t v_i_boxed_3307_; lean_object* v_res_3308_; 
v_sz_boxed_3306_ = lean_unbox_usize(v_sz_3292_);
lean_dec(v_sz_3292_);
v_i_boxed_3307_ = lean_unbox_usize(v_i_3293_);
lean_dec(v_i_3293_);
v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3290_, v_as_3291_, v_sz_boxed_3306_, v_i_boxed_3307_, v_b_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v_as_3291_);
lean_dec_ref(v_a_3290_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(lean_object* v_a_3309_, lean_object* v_inh_3310_, lean_object* v_n_3311_, lean_object* v_b_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
if (lean_obj_tag(v_n_3311_) == 0)
{
lean_object* v_cs_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3358_; 
v_cs_3324_ = lean_ctor_get(v_n_3311_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_n_3311_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3326_ = v_n_3311_;
v_isShared_3327_ = v_isSharedCheck_3358_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_cs_3324_);
lean_dec(v_n_3311_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3358_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; size_t v_sz_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v_b_3312_);
v_sz_3330_ = lean_array_size(v_cs_3324_);
v___x_3331_ = ((size_t)0ULL);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_a_3309_, v_inh_3310_, v_cs_3324_, v_sz_3330_, v___x_3331_, v___x_3329_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec_ref(v_cs_3324_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3349_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3349_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3349_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v_fst_3337_; 
v_fst_3337_ = lean_ctor_get(v_a_3333_, 0);
if (lean_obj_tag(v_fst_3337_) == 0)
{
lean_object* v_snd_3338_; lean_object* v___x_3340_; 
v_snd_3338_ = lean_ctor_get(v_a_3333_, 1);
lean_inc(v_snd_3338_);
lean_dec(v_a_3333_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set_tag(v___x_3326_, 1);
lean_ctor_set(v___x_3326_, 0, v_snd_3338_);
v___x_3340_ = v___x_3326_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_snd_3338_);
v___x_3340_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3342_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3340_);
v___x_3342_ = v___x_3335_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
else
{
lean_object* v_val_3345_; lean_object* v___x_3347_; 
lean_inc_ref(v_fst_3337_);
lean_dec(v_a_3333_);
lean_del_object(v___x_3326_);
v_val_3345_ = lean_ctor_get(v_fst_3337_, 0);
lean_inc(v_val_3345_);
lean_dec_ref(v_fst_3337_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v_val_3345_);
v___x_3347_ = v___x_3335_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_val_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_del_object(v___x_3326_);
v_a_3350_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3332_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3332_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
else
{
lean_object* v_vs_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3393_; 
v_vs_3359_ = lean_ctor_get(v_n_3311_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_n_3311_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3361_ = v_n_3311_;
v_isShared_3362_ = v_isSharedCheck_3393_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_vs_3359_);
lean_dec(v_n_3311_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3393_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; size_t v_sz_3365_; size_t v___x_3366_; lean_object* v___x_3367_; 
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v_b_3312_);
v_sz_3365_ = lean_array_size(v_vs_3359_);
v___x_3366_ = ((size_t)0ULL);
v___x_3367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3309_, v_vs_3359_, v_sz_3365_, v___x_3366_, v___x_3364_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec_ref(v_vs_3359_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3384_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3384_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3384_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_fst_3372_; 
v_fst_3372_ = lean_ctor_get(v_a_3368_, 0);
if (lean_obj_tag(v_fst_3372_) == 0)
{
lean_object* v_snd_3373_; lean_object* v___x_3375_; 
v_snd_3373_ = lean_ctor_get(v_a_3368_, 1);
lean_inc(v_snd_3373_);
lean_dec(v_a_3368_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v_snd_3373_);
v___x_3375_ = v___x_3361_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_snd_3373_);
v___x_3375_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3375_);
v___x_3377_ = v___x_3370_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
else
{
lean_object* v_val_3380_; lean_object* v___x_3382_; 
lean_inc_ref(v_fst_3372_);
lean_dec(v_a_3368_);
lean_del_object(v___x_3361_);
v_val_3380_ = lean_ctor_get(v_fst_3372_, 0);
lean_inc(v_val_3380_);
lean_dec_ref(v_fst_3372_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v_val_3380_);
v___x_3382_ = v___x_3370_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_val_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_del_object(v___x_3361_);
v_a_3385_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3367_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3367_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(lean_object* v_a_3394_, lean_object* v_inh_3395_, lean_object* v_as_3396_, size_t v_sz_3397_, size_t v_i_3398_, lean_object* v_b_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_usize_dec_lt(v_i_3398_, v_sz_3397_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v_b_3399_);
return v___x_3412_;
}
else
{
lean_object* v_snd_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3447_; 
v_snd_3413_ = lean_ctor_get(v_b_3399_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_b_3399_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; 
v_unused_3448_ = lean_ctor_get(v_b_3399_, 0);
lean_dec(v_unused_3448_);
v___x_3415_ = v_b_3399_;
v_isShared_3416_ = v_isSharedCheck_3447_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_snd_3413_);
lean_dec(v_b_3399_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3447_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_a_3417_; lean_object* v___x_3418_; 
v_a_3417_ = lean_array_uget_borrowed(v_as_3396_, v_i_3398_);
lean_inc(v_snd_3413_);
lean_inc(v_a_3417_);
v___x_3418_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_a_3394_, v_inh_3395_, v_a_3417_, v_snd_3413_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3438_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3438_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3438_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
if (lean_obj_tag(v_a_3419_) == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3423_, 0, v_a_3419_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3423_);
v___x_3425_ = v___x_3415_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v_snd_3413_);
v___x_3425_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3425_);
v___x_3427_ = v___x_3421_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_del_object(v___x_3421_);
lean_dec(v_snd_3413_);
v_a_3430_ = lean_ctor_get(v_a_3419_, 0);
lean_inc(v_a_3430_);
lean_dec_ref(v_a_3419_);
v___x_3431_ = lean_box(0);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v_a_3430_);
lean_ctor_set(v___x_3415_, 0, v___x_3431_);
v___x_3433_ = v___x_3415_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_a_3430_);
v___x_3433_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
size_t v___x_3434_; size_t v___x_3435_; 
v___x_3434_ = ((size_t)1ULL);
v___x_3435_ = lean_usize_add(v_i_3398_, v___x_3434_);
v_i_3398_ = v___x_3435_;
v_b_3399_ = v___x_3433_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_del_object(v___x_3415_);
lean_dec(v_snd_3413_);
v_a_3439_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3418_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3418_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_a_3449_ = _args[0];
lean_object* v_inh_3450_ = _args[1];
lean_object* v_as_3451_ = _args[2];
lean_object* v_sz_3452_ = _args[3];
lean_object* v_i_3453_ = _args[4];
lean_object* v_b_3454_ = _args[5];
lean_object* v___y_3455_ = _args[6];
lean_object* v___y_3456_ = _args[7];
lean_object* v___y_3457_ = _args[8];
lean_object* v___y_3458_ = _args[9];
lean_object* v___y_3459_ = _args[10];
lean_object* v___y_3460_ = _args[11];
lean_object* v___y_3461_ = _args[12];
lean_object* v___y_3462_ = _args[13];
lean_object* v___y_3463_ = _args[14];
lean_object* v___y_3464_ = _args[15];
lean_object* v___y_3465_ = _args[16];
_start:
{
size_t v_sz_boxed_3466_; size_t v_i_boxed_3467_; lean_object* v_res_3468_; 
v_sz_boxed_3466_ = lean_unbox_usize(v_sz_3452_);
lean_dec(v_sz_3452_);
v_i_boxed_3467_ = lean_unbox_usize(v_i_3453_);
lean_dec(v_i_3453_);
v_res_3468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_a_3449_, v_inh_3450_, v_as_3451_, v_sz_boxed_3466_, v_i_boxed_3467_, v_b_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v_as_3451_);
lean_dec(v_inh_3450_);
lean_dec_ref(v_a_3449_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1___boxed(lean_object* v_a_3469_, lean_object* v_inh_3470_, lean_object* v_n_3471_, lean_object* v_b_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_a_3469_, v_inh_3470_, v_n_3471_, v_b_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v_inh_3470_);
lean_dec_ref(v_a_3469_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(lean_object* v_a_3485_, lean_object* v_as_3486_, size_t v_sz_3487_, size_t v_i_3488_, lean_object* v_b_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
uint8_t v___x_3501_; 
v___x_3501_ = lean_usize_dec_lt(v_i_3488_, v_sz_3487_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_b_3489_);
return v___x_3502_;
}
else
{
lean_object* v_snd_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3566_; 
v_snd_3503_ = lean_ctor_get(v_b_3489_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_b_3489_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v_b_3489_, 0);
lean_dec(v_unused_3567_);
v___x_3505_ = v_b_3489_;
v_isShared_3506_ = v_isSharedCheck_3566_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_snd_3503_);
lean_dec(v_b_3489_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3566_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; lean_object* v_a_3509_; lean_object* v___y_3520_; lean_object* v_a_3550_; 
v___x_3507_ = lean_box(0);
v_a_3550_ = lean_array_uget_borrowed(v_as_3486_, v_i_3488_);
if (lean_obj_tag(v_a_3550_) == 1)
{
lean_object* v_val_3551_; lean_object* v_p_3552_; uint8_t v___x_3553_; 
v_val_3551_ = lean_ctor_get(v_a_3550_, 0);
v_p_3552_ = lean_ctor_get(v_val_3551_, 0);
v___x_3553_ = l_Int_Linear_Poly_isSorted(v_p_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3555_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3554_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
v___y_3520_ = v___x_3555_;
goto v___jp_3519_;
}
else
{
uint8_t v___x_3556_; 
v___x_3556_ = l_Int_Linear_Poly_checkCoeffs(v_p_3552_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3558_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3557_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
v___y_3520_ = v___x_3558_;
goto v___jp_3519_;
}
else
{
lean_object* v_elimStack_3559_; uint8_t v___x_3560_; 
v_elimStack_3559_ = lean_ctor_get(v_a_3485_, 11);
v___x_3560_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3503_, v_elimStack_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3562_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3561_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
v___y_3520_ = v___x_3562_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3563_ = l_Int_Linear_Poly_coeff(v_p_3552_, v_snd_3503_);
v___x_3564_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_3565_ = lean_int_dec_eq(v___x_3563_, v___x_3564_);
lean_dec(v___x_3563_);
if (v___x_3565_ == 0)
{
if (v___x_3560_ == 0)
{
goto v___jp_3547_;
}
else
{
goto v___jp_3516_;
}
}
else
{
goto v___jp_3547_;
}
}
}
}
}
else
{
goto v___jp_3516_;
}
v___jp_3508_:
{
lean_object* v___x_3511_; 
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v_a_3509_);
lean_ctor_set(v___x_3505_, 0, v___x_3507_);
v___x_3511_ = v___x_3505_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3507_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_a_3509_);
v___x_3511_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
size_t v___x_3512_; size_t v___x_3513_; 
v___x_3512_ = ((size_t)1ULL);
v___x_3513_ = lean_usize_add(v_i_3488_, v___x_3512_);
v_i_3488_ = v___x_3513_;
v_b_3489_ = v___x_3511_;
goto _start;
}
}
v___jp_3516_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_nat_add(v_snd_3503_, v___x_3517_);
lean_dec(v_snd_3503_);
v_a_3509_ = v___x_3518_;
goto v___jp_3508_;
}
v___jp_3519_:
{
if (lean_obj_tag(v___y_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3538_; 
v_a_3521_ = lean_ctor_get(v___y_3520_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___y_3520_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3523_ = v___y_3520_;
v_isShared_3524_ = v_isSharedCheck_3538_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___y_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3538_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
if (lean_obj_tag(v_a_3521_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3536_; 
lean_del_object(v___x_3505_);
v_a_3525_ = lean_ctor_get(v_a_3521_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3527_ = v_a_3521_;
v_isShared_3528_ = v_isSharedCheck_3536_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v_a_3521_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3536_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set_tag(v___x_3527_, 1);
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v_snd_3503_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3531_);
v___x_3533_ = v___x_3523_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v_a_3537_; 
lean_del_object(v___x_3523_);
lean_dec(v_snd_3503_);
v_a_3537_ = lean_ctor_get(v_a_3521_, 0);
lean_inc(v_a_3537_);
lean_dec_ref(v_a_3521_);
v_a_3509_ = v_a_3537_;
goto v___jp_3508_;
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_del_object(v___x_3505_);
lean_dec(v_snd_3503_);
v_a_3539_ = lean_ctor_get(v___y_3520_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___y_3520_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___y_3520_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___y_3520_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
v___jp_3547_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3549_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3548_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
v___y_3520_ = v___x_3549_;
goto v___jp_3519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5___boxed(lean_object* v_a_3568_, lean_object* v_as_3569_, lean_object* v_sz_3570_, lean_object* v_i_3571_, lean_object* v_b_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
size_t v_sz_boxed_3584_; size_t v_i_boxed_3585_; lean_object* v_res_3586_; 
v_sz_boxed_3584_ = lean_unbox_usize(v_sz_3570_);
lean_dec(v_sz_3570_);
v_i_boxed_3585_ = lean_unbox_usize(v_i_3571_);
lean_dec(v_i_3571_);
v_res_3586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3568_, v_as_3569_, v_sz_boxed_3584_, v_i_boxed_3585_, v_b_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v_as_3569_);
lean_dec_ref(v_a_3568_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(lean_object* v_a_3587_, lean_object* v_as_3588_, size_t v_sz_3589_, size_t v_i_3590_, lean_object* v_b_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
uint8_t v___x_3603_; 
v___x_3603_ = lean_usize_dec_lt(v_i_3590_, v_sz_3589_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; 
v___x_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3604_, 0, v_b_3591_);
return v___x_3604_;
}
else
{
lean_object* v_snd_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3668_; 
v_snd_3605_ = lean_ctor_get(v_b_3591_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_b_3591_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v_b_3591_, 0);
lean_dec(v_unused_3669_);
v___x_3607_ = v_b_3591_;
v_isShared_3608_ = v_isSharedCheck_3668_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_snd_3605_);
lean_dec(v_b_3591_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3668_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v_a_3611_; lean_object* v___y_3622_; lean_object* v_a_3652_; 
v___x_3609_ = lean_box(0);
v_a_3652_ = lean_array_uget_borrowed(v_as_3588_, v_i_3590_);
if (lean_obj_tag(v_a_3652_) == 1)
{
lean_object* v_val_3653_; lean_object* v_p_3654_; uint8_t v___x_3655_; 
v_val_3653_ = lean_ctor_get(v_a_3652_, 0);
v_p_3654_ = lean_ctor_get(v_val_3653_, 0);
v___x_3655_ = l_Int_Linear_Poly_isSorted(v_p_3654_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3657_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3656_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v___y_3622_ = v___x_3657_;
goto v___jp_3621_;
}
else
{
uint8_t v___x_3658_; 
v___x_3658_ = l_Int_Linear_Poly_checkCoeffs(v_p_3654_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3660_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3659_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v___y_3622_ = v___x_3660_;
goto v___jp_3621_;
}
else
{
lean_object* v_elimStack_3661_; uint8_t v___x_3662_; 
v_elimStack_3661_ = lean_ctor_get(v_a_3587_, 11);
v___x_3662_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3605_, v_elimStack_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3664_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3663_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v___y_3622_ = v___x_3664_;
goto v___jp_3621_;
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___x_3665_ = l_Int_Linear_Poly_coeff(v_p_3654_, v_snd_3605_);
v___x_3666_ = lean_obj_once(&l_Int_Linear_Poly_checkCoeffs___closed__0, &l_Int_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Linear_Poly_checkCoeffs___closed__0);
v___x_3667_ = lean_int_dec_eq(v___x_3665_, v___x_3666_);
lean_dec(v___x_3665_);
if (v___x_3667_ == 0)
{
if (v___x_3662_ == 0)
{
goto v___jp_3649_;
}
else
{
goto v___jp_3618_;
}
}
else
{
goto v___jp_3649_;
}
}
}
}
}
else
{
goto v___jp_3618_;
}
v___jp_3610_:
{
lean_object* v___x_3613_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 1, v_a_3611_);
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3613_ = v___x_3607_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_a_3611_);
v___x_3613_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
size_t v___x_3614_; size_t v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((size_t)1ULL);
v___x_3615_ = lean_usize_add(v_i_3590_, v___x_3614_);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3587_, v_as_3588_, v_sz_3589_, v___x_3615_, v___x_3613_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3616_;
}
}
v___jp_3618_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = lean_unsigned_to_nat(1u);
v___x_3620_ = lean_nat_add(v_snd_3605_, v___x_3619_);
lean_dec(v_snd_3605_);
v_a_3611_ = v___x_3620_;
goto v___jp_3610_;
}
v___jp_3621_:
{
if (lean_obj_tag(v___y_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3640_; 
v_a_3623_ = lean_ctor_get(v___y_3622_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___y_3622_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3625_ = v___y_3622_;
v_isShared_3626_ = v_isSharedCheck_3640_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___y_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3640_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
if (lean_obj_tag(v_a_3623_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3638_; 
lean_del_object(v___x_3607_);
v_a_3627_ = lean_ctor_get(v_a_3623_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_a_3623_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3629_ = v_a_3623_;
v_isShared_3630_ = v_isSharedCheck_3638_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v_a_3623_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3638_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set_tag(v___x_3629_, 1);
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set(v___x_3633_, 1, v_snd_3605_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 0, v___x_3633_);
v___x_3635_ = v___x_3625_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_object* v_a_3639_; 
lean_del_object(v___x_3625_);
lean_dec(v_snd_3605_);
v_a_3639_ = lean_ctor_get(v_a_3623_, 0);
lean_inc(v_a_3639_);
lean_dec_ref(v_a_3623_);
v_a_3611_ = v_a_3639_;
goto v___jp_3610_;
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_del_object(v___x_3607_);
lean_dec(v_snd_3605_);
v_a_3641_ = lean_ctor_get(v___y_3622_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___y_3622_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___y_3622_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___y_3622_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
v___jp_3649_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3651_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3650_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v___y_3622_ = v___x_3651_;
goto v___jp_3621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2___boxed(lean_object* v_a_3670_, lean_object* v_as_3671_, lean_object* v_sz_3672_, lean_object* v_i_3673_, lean_object* v_b_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
size_t v_sz_boxed_3686_; size_t v_i_boxed_3687_; lean_object* v_res_3688_; 
v_sz_boxed_3686_ = lean_unbox_usize(v_sz_3672_);
lean_dec(v_sz_3672_);
v_i_boxed_3687_ = lean_unbox_usize(v_i_3673_);
lean_dec(v_i_3673_);
v_res_3688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3670_, v_as_3671_, v_sz_boxed_3686_, v_i_boxed_3687_, v_b_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v_as_3671_);
lean_dec_ref(v_a_3670_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(lean_object* v_a_3689_, lean_object* v_t_3690_, lean_object* v_init_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_root_3703_; lean_object* v_tail_3704_; lean_object* v___x_3705_; 
v_root_3703_ = lean_ctor_get(v_t_3690_, 0);
lean_inc_ref(v_root_3703_);
v_tail_3704_ = lean_ctor_get(v_t_3690_, 1);
lean_inc_ref(v_tail_3704_);
lean_dec_ref(v_t_3690_);
lean_inc(v_init_3691_);
v___x_3705_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_a_3689_, v_init_3691_, v_root_3703_, v_init_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v_init_3691_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3742_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3742_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3742_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
if (lean_obj_tag(v_a_3706_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3712_; 
lean_dec_ref(v_tail_3704_);
v_a_3710_ = lean_ctor_get(v_a_3706_, 0);
lean_inc(v_a_3710_);
lean_dec_ref(v_a_3706_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v_a_3710_);
v___x_3712_ = v___x_3708_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3710_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; size_t v_sz_3717_; size_t v___x_3718_; lean_object* v___x_3719_; 
lean_del_object(v___x_3708_);
v_a_3714_ = lean_ctor_get(v_a_3706_, 0);
lean_inc(v_a_3714_);
lean_dec_ref(v_a_3706_);
v___x_3715_ = lean_box(0);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v_a_3714_);
v_sz_3717_ = lean_array_size(v_tail_3704_);
v___x_3718_ = ((size_t)0ULL);
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3689_, v_tail_3704_, v_sz_3717_, v___x_3718_, v___x_3716_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec_ref(v_tail_3704_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3733_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3733_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3733_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v_fst_3724_; 
v_fst_3724_ = lean_ctor_get(v_a_3720_, 0);
if (lean_obj_tag(v_fst_3724_) == 0)
{
lean_object* v_snd_3725_; lean_object* v___x_3727_; 
v_snd_3725_ = lean_ctor_get(v_a_3720_, 1);
lean_inc(v_snd_3725_);
lean_dec(v_a_3720_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v_snd_3725_);
v___x_3727_ = v___x_3722_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_snd_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
else
{
lean_object* v_val_3729_; lean_object* v___x_3731_; 
lean_inc_ref(v_fst_3724_);
lean_dec(v_a_3720_);
v_val_3729_ = lean_ctor_get(v_fst_3724_, 0);
lean_inc(v_val_3729_);
lean_dec_ref(v_fst_3724_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v_val_3729_);
v___x_3731_ = v___x_3722_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_val_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
v_a_3734_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3719_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3719_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v_tail_3704_);
v_a_3743_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3705_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3705_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1___boxed(lean_object* v_a_3751_, lean_object* v_t_3752_, lean_object* v_init_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3751_, v_t_3752_, v_init_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v_a_3751_);
return v_res_3765_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3767_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0));
v___x_3768_ = lean_unsigned_to_nat(2u);
v___x_3769_ = lean_unsigned_to_nat(87u);
v___x_3770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3771_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3772_ = l_mkPanicMessageWithDecl(v___x_3771_, v___x_3770_, v___x_3769_, v___x_3768_, v___x_3767_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3773_, v_a_3781_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v_elimEqs_3786_; lean_object* v_vars_3787_; lean_object* v_size_3788_; lean_object* v_size_3789_; uint8_t v___x_3790_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref(v___x_3784_);
v_elimEqs_3786_ = lean_ctor_get(v_a_3785_, 10);
lean_inc_ref(v_elimEqs_3786_);
v_vars_3787_ = lean_ctor_get(v_a_3785_, 0);
v_size_3788_ = lean_ctor_get(v_elimEqs_3786_, 2);
v_size_3789_ = lean_ctor_get(v_vars_3787_, 2);
v___x_3790_ = lean_nat_dec_eq(v_size_3788_, v_size_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_dec_ref(v_elimEqs_3786_);
lean_dec(v_a_3785_);
v___x_3791_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1);
v___x_3792_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_3791_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
return v___x_3792_;
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = lean_unsigned_to_nat(0u);
v___x_3794_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3785_, v_elimEqs_3786_, v___x_3793_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
lean_dec(v_a_3785_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3802_; 
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; 
v_unused_3803_ = lean_ctor_get(v___x_3794_, 0);
lean_dec(v_unused_3803_);
v___x_3796_ = v___x_3794_;
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
else
{
lean_dec(v___x_3794_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3798_ = lean_box(0);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3798_);
v___x_3800_ = v___x_3796_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
v_a_3804_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3794_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3794_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
v_a_3812_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3784_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3784_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___boxed(lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_a_3825_);
lean_dec_ref(v_a_3824_);
lean_dec(v_a_3823_);
lean_dec_ref(v_a_3822_);
lean_dec(v_a_3821_);
lean_dec(v_a_3820_);
return v_res_3831_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1));
v___x_3835_ = lean_unsigned_to_nat(4u);
v___x_3836_ = lean_unsigned_to_nat(99u);
v___x_3837_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0));
v___x_3838_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_3839_ = l_mkPanicMessageWithDecl(v___x_3838_, v___x_3837_, v___x_3836_, v___x_3835_, v___x_3834_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(lean_object* v_as_x27_3840_, lean_object* v_b_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
if (lean_obj_tag(v_as_x27_3840_) == 0)
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_b_3841_);
return v___x_3853_;
}
else
{
lean_object* v_head_3854_; lean_object* v_tail_3855_; lean_object* v___x_3856_; 
v_head_3854_ = lean_ctor_get(v_as_x27_3840_, 0);
v_tail_3855_ = lean_ctor_get(v_as_x27_3840_, 1);
v___x_3856_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_head_3854_, v___y_3842_, v___y_3850_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; uint8_t v___x_3858_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3856_);
v___x_3858_ = lean_unbox(v_a_3857_);
lean_dec(v_a_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2);
v___x_3860_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_3859_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3871_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
if (lean_obj_tag(v_a_3861_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; 
v_a_3865_ = lean_ctor_get(v_a_3861_, 0);
lean_inc(v_a_3865_);
lean_dec_ref(v_a_3861_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v_a_3865_);
v___x_3867_ = v___x_3863_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
else
{
lean_object* v_a_3869_; 
lean_del_object(v___x_3863_);
v_a_3869_ = lean_ctor_get(v_a_3861_, 0);
lean_inc(v_a_3869_);
lean_dec_ref(v_a_3861_);
v_as_x27_3840_ = v_tail_3855_;
v_b_3841_ = v_a_3869_;
goto _start;
}
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_a_3872_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3860_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3860_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_object* v___x_3880_; 
v___x_3880_ = lean_box(0);
v_as_x27_3840_ = v_tail_3855_;
v_b_3841_ = v___x_3880_;
goto _start;
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_a_3882_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3856_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3856_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___boxed(lean_object* v_as_x27_3890_, lean_object* v_b_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3890_, v_b_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec(v_as_x27_3890_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3904_, v_a_3912_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v_elimStack_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3915_);
v_elimStack_3917_ = lean_ctor_get(v_a_3916_, 11);
lean_inc(v_elimStack_3917_);
lean_dec(v_a_3916_);
v___x_3918_ = lean_box(0);
v___x_3919_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_elimStack_3917_, v___x_3918_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_elimStack_3917_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3926_ == 0)
{
lean_object* v_unused_3927_; 
v_unused_3927_ = lean_ctor_get(v___x_3919_, 0);
lean_dec(v_unused_3927_);
v___x_3921_ = v___x_3919_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_dec(v___x_3919_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3918_);
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3918_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
else
{
return v___x_3919_;
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_a_3928_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3915_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3915_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack___boxed(lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec(v_a_3936_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(lean_object* v_as_3948_, lean_object* v_as_x27_3949_, lean_object* v_b_3950_, lean_object* v_a_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3949_, v_b_3950_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___boxed(lean_object* v_as_3964_, lean_object* v_as_x27_3965_, lean_object* v_b_3966_, lean_object* v_a_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(v_as_3964_, v_as_x27_3965_, v_b_3966_, v_a_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec(v_as_x27_3965_);
lean_dec(v_as_3964_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_3983_, lean_object* v_as_3984_, size_t v_sz_3985_, size_t v_i_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
uint8_t v___x_3999_; 
v___x_3999_ = lean_usize_dec_lt(v_i_3986_, v_sz_3985_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_b_3987_);
return v___x_4000_;
}
else
{
lean_object* v_a_4001_; lean_object* v_p_4002_; lean_object* v___x_4003_; 
lean_dec_ref(v_b_3987_);
v_a_4001_ = lean_array_uget_borrowed(v_as_3984_, v_i_3986_);
v_p_4002_ = lean_ctor_get(v_a_4001_, 0);
v___x_4003_ = l_Int_Linear_Poly_checkCnstrOf(v_p_4002_, v_____s_3983_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v___x_4004_; size_t v___x_4005_; size_t v___x_4006_; 
lean_dec_ref(v___x_4003_);
v___x_4004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_4005_ = ((size_t)1ULL);
v___x_4006_ = lean_usize_add(v_i_3986_, v___x_4005_);
v_i_3986_ = v___x_4006_;
v_b_3987_ = v___x_4004_;
goto _start;
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
v_a_4008_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_4003_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4003_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object* v_____s_4016_, lean_object* v_as_4017_, lean_object* v_sz_4018_, lean_object* v_i_4019_, lean_object* v_b_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
size_t v_sz_boxed_4032_; size_t v_i_boxed_4033_; lean_object* v_res_4034_; 
v_sz_boxed_4032_ = lean_unbox_usize(v_sz_4018_);
lean_dec(v_sz_4018_);
v_i_boxed_4033_ = lean_unbox_usize(v_i_4019_);
lean_dec(v_i_4019_);
v_res_4034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_4016_, v_as_4017_, v_sz_boxed_4032_, v_i_boxed_4033_, v_b_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v_as_4017_);
lean_dec(v_____s_4016_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_4035_, lean_object* v_as_4036_, size_t v_sz_4037_, size_t v_i_4038_, lean_object* v_b_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
uint8_t v___x_4051_; 
v___x_4051_ = lean_usize_dec_lt(v_i_4038_, v_sz_4037_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v_b_4039_);
return v___x_4052_;
}
else
{
lean_object* v_a_4053_; lean_object* v_p_4054_; lean_object* v___x_4055_; 
lean_dec_ref(v_b_4039_);
v_a_4053_ = lean_array_uget_borrowed(v_as_4036_, v_i_4038_);
v_p_4054_ = lean_ctor_get(v_a_4053_, 0);
v___x_4055_ = l_Int_Linear_Poly_checkCnstrOf(v_p_4054_, v_____s_4035_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v___x_4056_; size_t v___x_4057_; size_t v___x_4058_; lean_object* v___x_4059_; 
lean_dec_ref(v___x_4055_);
v___x_4056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_4057_ = ((size_t)1ULL);
v___x_4058_ = lean_usize_add(v_i_4038_, v___x_4057_);
v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_4035_, v_as_4036_, v_sz_4037_, v___x_4058_, v___x_4056_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
return v___x_4059_;
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
v_a_4060_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4055_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4055_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object* v_____s_4068_, lean_object* v_as_4069_, lean_object* v_sz_4070_, lean_object* v_i_4071_, lean_object* v_b_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
size_t v_sz_boxed_4084_; size_t v_i_boxed_4085_; lean_object* v_res_4086_; 
v_sz_boxed_4084_ = lean_unbox_usize(v_sz_4070_);
lean_dec(v_sz_4070_);
v_i_boxed_4085_ = lean_unbox_usize(v_i_4071_);
lean_dec(v_i_4071_);
v_res_4086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4068_, v_as_4069_, v_sz_boxed_4084_, v_i_boxed_4085_, v_b_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v_as_4069_);
lean_dec(v_____s_4068_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_4090_, lean_object* v_as_4091_, size_t v_sz_4092_, size_t v_i_4093_, lean_object* v_b_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
uint8_t v___x_4106_; 
v___x_4106_ = lean_usize_dec_lt(v_i_4093_, v_sz_4092_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_b_4094_);
return v___x_4107_;
}
else
{
lean_object* v_a_4108_; lean_object* v_p_4109_; lean_object* v___x_4110_; 
lean_dec_ref(v_b_4094_);
v_a_4108_ = lean_array_uget_borrowed(v_as_4091_, v_i_4093_);
v_p_4109_ = lean_ctor_get(v_a_4108_, 0);
v___x_4110_ = l_Int_Linear_Poly_checkCnstrOf(v_p_4109_, v_____s_4090_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v___x_4111_; size_t v___x_4112_; size_t v___x_4113_; 
lean_dec_ref(v___x_4110_);
v___x_4111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4112_ = ((size_t)1ULL);
v___x_4113_ = lean_usize_add(v_i_4093_, v___x_4112_);
v_i_4093_ = v___x_4113_;
v_b_4094_ = v___x_4111_;
goto _start;
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
v_a_4115_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4110_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4110_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_____s_4123_, lean_object* v_as_4124_, lean_object* v_sz_4125_, lean_object* v_i_4126_, lean_object* v_b_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
size_t v_sz_boxed_4139_; size_t v_i_boxed_4140_; lean_object* v_res_4141_; 
v_sz_boxed_4139_ = lean_unbox_usize(v_sz_4125_);
lean_dec(v_sz_4125_);
v_i_boxed_4140_ = lean_unbox_usize(v_i_4126_);
lean_dec(v_i_4126_);
v_res_4141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4123_, v_as_4124_, v_sz_boxed_4139_, v_i_boxed_4140_, v_b_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v_as_4124_);
lean_dec(v_____s_4123_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_4142_, lean_object* v_as_4143_, size_t v_sz_4144_, size_t v_i_4145_, lean_object* v_b_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
uint8_t v___x_4158_; 
v___x_4158_ = lean_usize_dec_lt(v_i_4145_, v_sz_4144_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4159_; 
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v_b_4146_);
return v___x_4159_;
}
else
{
lean_object* v_a_4160_; lean_object* v_p_4161_; lean_object* v___x_4162_; 
lean_dec_ref(v_b_4146_);
v_a_4160_ = lean_array_uget_borrowed(v_as_4143_, v_i_4145_);
v_p_4161_ = lean_ctor_get(v_a_4160_, 0);
v___x_4162_ = l_Int_Linear_Poly_checkCnstrOf(v_p_4161_, v_____s_4142_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v___x_4163_; size_t v___x_4164_; size_t v___x_4165_; lean_object* v___x_4166_; 
lean_dec_ref(v___x_4162_);
v___x_4163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4164_ = ((size_t)1ULL);
v___x_4165_ = lean_usize_add(v_i_4145_, v___x_4164_);
v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4142_, v_as_4143_, v_sz_4144_, v___x_4165_, v___x_4163_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4166_;
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
v_a_4167_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4162_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4162_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_____s_4175_, lean_object* v_as_4176_, lean_object* v_sz_4177_, lean_object* v_i_4178_, lean_object* v_b_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
size_t v_sz_boxed_4191_; size_t v_i_boxed_4192_; lean_object* v_res_4193_; 
v_sz_boxed_4191_ = lean_unbox_usize(v_sz_4177_);
lean_dec(v_sz_4177_);
v_i_boxed_4192_ = lean_unbox_usize(v_i_4178_);
lean_dec(v_i_4178_);
v_res_4193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4175_, v_as_4176_, v_sz_boxed_4191_, v_i_boxed_4192_, v_b_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v_as_4176_);
lean_dec(v_____s_4175_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_____s_4194_, lean_object* v_inh_4195_, lean_object* v_n_4196_, lean_object* v_b_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
if (lean_obj_tag(v_n_4196_) == 0)
{
lean_object* v_cs_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4243_; 
v_cs_4209_ = lean_ctor_get(v_n_4196_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v_n_4196_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4211_ = v_n_4196_;
v_isShared_4212_ = v_isSharedCheck_4243_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_cs_4209_);
lean_dec(v_n_4196_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4243_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; size_t v_sz_4215_; size_t v___x_4216_; lean_object* v___x_4217_; 
v___x_4213_ = lean_box(0);
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
lean_ctor_set(v___x_4214_, 1, v_b_4197_);
v_sz_4215_ = lean_array_size(v_cs_4209_);
v___x_4216_ = ((size_t)0ULL);
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_____s_4194_, v_inh_4195_, v_cs_4209_, v_sz_4215_, v___x_4216_, v___x_4214_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
lean_dec_ref(v_cs_4209_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4234_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4220_ = v___x_4217_;
v_isShared_4221_ = v_isSharedCheck_4234_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4234_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v_fst_4222_; 
v_fst_4222_ = lean_ctor_get(v_a_4218_, 0);
if (lean_obj_tag(v_fst_4222_) == 0)
{
lean_object* v_snd_4223_; lean_object* v___x_4225_; 
v_snd_4223_ = lean_ctor_get(v_a_4218_, 1);
lean_inc(v_snd_4223_);
lean_dec(v_a_4218_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 1);
lean_ctor_set(v___x_4211_, 0, v_snd_4223_);
v___x_4225_ = v___x_4211_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_snd_4223_);
v___x_4225_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
lean_object* v___x_4227_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4225_);
v___x_4227_ = v___x_4220_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
else
{
lean_object* v_val_4230_; lean_object* v___x_4232_; 
lean_inc_ref(v_fst_4222_);
lean_dec(v_a_4218_);
lean_del_object(v___x_4211_);
v_val_4230_ = lean_ctor_get(v_fst_4222_, 0);
lean_inc(v_val_4230_);
lean_dec_ref(v_fst_4222_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v_val_4230_);
v___x_4232_ = v___x_4220_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_val_4230_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_del_object(v___x_4211_);
v_a_4235_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4217_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4217_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
else
{
lean_object* v_vs_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4278_; 
v_vs_4244_ = lean_ctor_get(v_n_4196_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v_n_4196_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4246_ = v_n_4196_;
v_isShared_4247_ = v_isSharedCheck_4278_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_vs_4244_);
lean_dec(v_n_4196_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4278_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; size_t v_sz_4250_; size_t v___x_4251_; lean_object* v___x_4252_; 
v___x_4248_ = lean_box(0);
v___x_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4248_);
lean_ctor_set(v___x_4249_, 1, v_b_4197_);
v_sz_4250_ = lean_array_size(v_vs_4244_);
v___x_4251_ = ((size_t)0ULL);
v___x_4252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4194_, v_vs_4244_, v_sz_4250_, v___x_4251_, v___x_4249_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
lean_dec_ref(v_vs_4244_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4269_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4255_ = v___x_4252_;
v_isShared_4256_ = v_isSharedCheck_4269_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4269_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v_fst_4257_; 
v_fst_4257_ = lean_ctor_get(v_a_4253_, 0);
if (lean_obj_tag(v_fst_4257_) == 0)
{
lean_object* v_snd_4258_; lean_object* v___x_4260_; 
v_snd_4258_ = lean_ctor_get(v_a_4253_, 1);
lean_inc(v_snd_4258_);
lean_dec(v_a_4253_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v_snd_4258_);
v___x_4260_ = v___x_4246_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_snd_4258_);
v___x_4260_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
lean_object* v___x_4262_; 
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4260_);
v___x_4262_ = v___x_4255_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
else
{
lean_object* v_val_4265_; lean_object* v___x_4267_; 
lean_inc_ref(v_fst_4257_);
lean_dec(v_a_4253_);
lean_del_object(v___x_4246_);
v_val_4265_ = lean_ctor_get(v_fst_4257_, 0);
lean_inc(v_val_4265_);
lean_dec_ref(v_fst_4257_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v_val_4265_);
v___x_4267_ = v___x_4255_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_val_4265_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_del_object(v___x_4246_);
v_a_4270_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4252_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4252_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_____s_4279_, lean_object* v_inh_4280_, lean_object* v_as_4281_, size_t v_sz_4282_, size_t v_i_4283_, lean_object* v_b_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
uint8_t v___x_4296_; 
v___x_4296_ = lean_usize_dec_lt(v_i_4283_, v_sz_4282_);
if (v___x_4296_ == 0)
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4297_, 0, v_b_4284_);
return v___x_4297_;
}
else
{
lean_object* v_snd_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4332_; 
v_snd_4298_ = lean_ctor_get(v_b_4284_, 1);
v_isSharedCheck_4332_ = !lean_is_exclusive(v_b_4284_);
if (v_isSharedCheck_4332_ == 0)
{
lean_object* v_unused_4333_; 
v_unused_4333_ = lean_ctor_get(v_b_4284_, 0);
lean_dec(v_unused_4333_);
v___x_4300_ = v_b_4284_;
v_isShared_4301_ = v_isSharedCheck_4332_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_snd_4298_);
lean_dec(v_b_4284_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4332_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v_a_4302_; lean_object* v___x_4303_; 
v_a_4302_ = lean_array_uget_borrowed(v_as_4281_, v_i_4283_);
lean_inc(v_snd_4298_);
lean_inc(v_a_4302_);
v___x_4303_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_____s_4279_, v_inh_4280_, v_a_4302_, v_snd_4298_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4323_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4323_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4323_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
if (lean_obj_tag(v_a_4304_) == 0)
{
lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4308_, 0, v_a_4304_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v___x_4308_);
v___x_4310_ = v___x_4300_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4314_, 1, v_snd_4298_);
v___x_4310_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4312_; 
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 0, v___x_4310_);
v___x_4312_ = v___x_4306_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
lean_del_object(v___x_4306_);
lean_dec(v_snd_4298_);
v_a_4315_ = lean_ctor_get(v_a_4304_, 0);
lean_inc(v_a_4315_);
lean_dec_ref(v_a_4304_);
v___x_4316_ = lean_box(0);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 1, v_a_4315_);
lean_ctor_set(v___x_4300_, 0, v___x_4316_);
v___x_4318_ = v___x_4300_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4316_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_a_4315_);
v___x_4318_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
size_t v___x_4319_; size_t v___x_4320_; 
v___x_4319_ = ((size_t)1ULL);
v___x_4320_ = lean_usize_add(v_i_4283_, v___x_4319_);
v_i_4283_ = v___x_4320_;
v_b_4284_ = v___x_4318_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_del_object(v___x_4300_);
lean_dec(v_snd_4298_);
v_a_4324_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4303_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4303_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_____s_4334_ = _args[0];
lean_object* v_inh_4335_ = _args[1];
lean_object* v_as_4336_ = _args[2];
lean_object* v_sz_4337_ = _args[3];
lean_object* v_i_4338_ = _args[4];
lean_object* v_b_4339_ = _args[5];
lean_object* v___y_4340_ = _args[6];
lean_object* v___y_4341_ = _args[7];
lean_object* v___y_4342_ = _args[8];
lean_object* v___y_4343_ = _args[9];
lean_object* v___y_4344_ = _args[10];
lean_object* v___y_4345_ = _args[11];
lean_object* v___y_4346_ = _args[12];
lean_object* v___y_4347_ = _args[13];
lean_object* v___y_4348_ = _args[14];
lean_object* v___y_4349_ = _args[15];
lean_object* v___y_4350_ = _args[16];
_start:
{
size_t v_sz_boxed_4351_; size_t v_i_boxed_4352_; lean_object* v_res_4353_; 
v_sz_boxed_4351_ = lean_unbox_usize(v_sz_4337_);
lean_dec(v_sz_4337_);
v_i_boxed_4352_ = lean_unbox_usize(v_i_4338_);
lean_dec(v_i_4338_);
v_res_4353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_____s_4334_, v_inh_4335_, v_as_4336_, v_sz_boxed_4351_, v_i_boxed_4352_, v_b_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v_as_4336_);
lean_dec(v_____s_4334_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_____s_4354_, lean_object* v_inh_4355_, lean_object* v_n_4356_, lean_object* v_b_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_____s_4354_, v_inh_4355_, v_n_4356_, v_b_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec(v_____s_4354_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(lean_object* v_____s_4370_, lean_object* v_t_4371_, lean_object* v_init_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v_root_4384_; lean_object* v_tail_4385_; lean_object* v___x_4386_; 
v_root_4384_ = lean_ctor_get(v_t_4371_, 0);
lean_inc_ref(v_root_4384_);
v_tail_4385_ = lean_ctor_get(v_t_4371_, 1);
lean_inc_ref(v_tail_4385_);
lean_dec_ref(v_t_4371_);
v___x_4386_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_____s_4370_, v_init_4372_, v_root_4384_, v_init_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4423_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4389_ = v___x_4386_;
v_isShared_4390_ = v_isSharedCheck_4423_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4386_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4423_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
if (lean_obj_tag(v_a_4387_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4393_; 
lean_dec_ref(v_tail_4385_);
v_a_4391_ = lean_ctor_get(v_a_4387_, 0);
lean_inc(v_a_4391_);
lean_dec_ref(v_a_4387_);
if (v_isShared_4390_ == 0)
{
lean_ctor_set(v___x_4389_, 0, v_a_4391_);
v___x_4393_ = v___x_4389_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; size_t v_sz_4398_; size_t v___x_4399_; lean_object* v___x_4400_; 
lean_del_object(v___x_4389_);
v_a_4395_ = lean_ctor_get(v_a_4387_, 0);
lean_inc(v_a_4395_);
lean_dec_ref(v_a_4387_);
v___x_4396_ = lean_box(0);
v___x_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v_a_4395_);
v_sz_4398_ = lean_array_size(v_tail_4385_);
v___x_4399_ = ((size_t)0ULL);
v___x_4400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4370_, v_tail_4385_, v_sz_4398_, v___x_4399_, v___x_4397_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec_ref(v_tail_4385_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4414_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4403_ = v___x_4400_;
v_isShared_4404_ = v_isSharedCheck_4414_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4414_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v_fst_4405_; 
v_fst_4405_ = lean_ctor_get(v_a_4401_, 0);
if (lean_obj_tag(v_fst_4405_) == 0)
{
lean_object* v_snd_4406_; lean_object* v___x_4408_; 
v_snd_4406_ = lean_ctor_get(v_a_4401_, 1);
lean_inc(v_snd_4406_);
lean_dec(v_a_4401_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v_snd_4406_);
v___x_4408_ = v___x_4403_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_snd_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
else
{
lean_object* v_val_4410_; lean_object* v___x_4412_; 
lean_inc_ref(v_fst_4405_);
lean_dec(v_a_4401_);
v_val_4410_ = lean_ctor_get(v_fst_4405_, 0);
lean_inc(v_val_4410_);
lean_dec_ref(v_fst_4405_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v_val_4410_);
v___x_4412_ = v___x_4403_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_val_4410_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
v_a_4415_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4400_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4400_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec_ref(v_tail_4385_);
v_a_4424_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4386_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4386_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_4432_, lean_object* v_t_4433_, lean_object* v_init_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_____s_4432_, v_t_4433_, v_init_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec(v_____s_4432_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_4447_, size_t v_sz_4448_, size_t v_i_4449_, lean_object* v_b_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
uint8_t v___x_4462_; 
v___x_4462_ = lean_usize_dec_lt(v_i_4449_, v_sz_4448_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v_b_4450_);
return v___x_4463_;
}
else
{
lean_object* v_snd_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4488_; 
v_snd_4464_ = lean_ctor_get(v_b_4450_, 1);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_b_4450_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; 
v_unused_4489_ = lean_ctor_get(v_b_4450_, 0);
lean_dec(v_unused_4489_);
v___x_4466_ = v_b_4450_;
v_isShared_4467_ = v_isSharedCheck_4488_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_snd_4464_);
lean_dec(v_b_4450_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4488_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v_a_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v_a_4468_ = lean_array_uget_borrowed(v_as_4447_, v_i_4449_);
v___x_4469_ = lean_box(0);
lean_inc(v_a_4468_);
v___x_4470_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4464_, v_a_4468_, v___x_4469_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4475_; 
lean_dec_ref(v___x_4470_);
v___x_4471_ = lean_box(0);
v___x_4472_ = lean_unsigned_to_nat(1u);
v___x_4473_ = lean_nat_add(v_snd_4464_, v___x_4472_);
lean_dec(v_snd_4464_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 1, v___x_4473_);
lean_ctor_set(v___x_4466_, 0, v___x_4471_);
v___x_4475_ = v___x_4466_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
size_t v___x_4476_; size_t v___x_4477_; 
v___x_4476_ = ((size_t)1ULL);
v___x_4477_ = lean_usize_add(v_i_4449_, v___x_4476_);
v_i_4449_ = v___x_4477_;
v_b_4450_ = v___x_4475_;
goto _start;
}
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
lean_del_object(v___x_4466_);
lean_dec(v_snd_4464_);
v_a_4480_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4482_ = v___x_4470_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4470_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_4490_, lean_object* v_sz_4491_, lean_object* v_i_4492_, lean_object* v_b_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
size_t v_sz_boxed_4505_; size_t v_i_boxed_4506_; lean_object* v_res_4507_; 
v_sz_boxed_4505_ = lean_unbox_usize(v_sz_4491_);
lean_dec(v_sz_4491_);
v_i_boxed_4506_ = lean_unbox_usize(v_i_4492_);
lean_dec(v_i_4492_);
v_res_4507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4490_, v_sz_boxed_4505_, v_i_boxed_4506_, v_b_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v_as_4490_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_4508_, size_t v_sz_4509_, size_t v_i_4510_, lean_object* v_b_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
uint8_t v___x_4523_; 
v___x_4523_ = lean_usize_dec_lt(v_i_4510_, v_sz_4509_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; 
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v_b_4511_);
return v___x_4524_;
}
else
{
lean_object* v_snd_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4549_; 
v_snd_4525_ = lean_ctor_get(v_b_4511_, 1);
v_isSharedCheck_4549_ = !lean_is_exclusive(v_b_4511_);
if (v_isSharedCheck_4549_ == 0)
{
lean_object* v_unused_4550_; 
v_unused_4550_ = lean_ctor_get(v_b_4511_, 0);
lean_dec(v_unused_4550_);
v___x_4527_ = v_b_4511_;
v_isShared_4528_ = v_isSharedCheck_4549_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_snd_4525_);
lean_dec(v_b_4511_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4549_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v_a_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v_a_4529_ = lean_array_uget_borrowed(v_as_4508_, v_i_4510_);
v___x_4530_ = lean_box(0);
lean_inc(v_a_4529_);
v___x_4531_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4525_, v_a_4529_, v___x_4530_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4536_; 
lean_dec_ref(v___x_4531_);
v___x_4532_ = lean_box(0);
v___x_4533_ = lean_unsigned_to_nat(1u);
v___x_4534_ = lean_nat_add(v_snd_4525_, v___x_4533_);
lean_dec(v_snd_4525_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 1, v___x_4534_);
lean_ctor_set(v___x_4527_, 0, v___x_4532_);
v___x_4536_ = v___x_4527_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4532_);
lean_ctor_set(v_reuseFailAlloc_4540_, 1, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
size_t v___x_4537_; size_t v___x_4538_; lean_object* v___x_4539_; 
v___x_4537_ = ((size_t)1ULL);
v___x_4538_ = lean_usize_add(v_i_4510_, v___x_4537_);
v___x_4539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4508_, v_sz_4509_, v___x_4538_, v___x_4536_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
return v___x_4539_;
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
lean_del_object(v___x_4527_);
lean_dec(v_snd_4525_);
v_a_4541_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4531_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4531_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_4551_, lean_object* v_sz_4552_, lean_object* v_i_4553_, lean_object* v_b_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
size_t v_sz_boxed_4566_; size_t v_i_boxed_4567_; lean_object* v_res_4568_; 
v_sz_boxed_4566_ = lean_unbox_usize(v_sz_4552_);
lean_dec(v_sz_4552_);
v_i_boxed_4567_ = lean_unbox_usize(v_i_4553_);
lean_dec(v_i_4553_);
v_res_4568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_4551_, v_sz_boxed_4566_, v_i_boxed_4567_, v_b_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v_as_4551_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_inh_4569_, lean_object* v_n_4570_, lean_object* v_b_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
if (lean_obj_tag(v_n_4570_) == 0)
{
lean_object* v_cs_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4617_; 
v_cs_4583_ = lean_ctor_get(v_n_4570_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v_n_4570_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4585_ = v_n_4570_;
v_isShared_4586_ = v_isSharedCheck_4617_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_cs_4583_);
lean_dec(v_n_4570_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4617_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; size_t v_sz_4589_; size_t v___x_4590_; lean_object* v___x_4591_; 
v___x_4587_ = lean_box(0);
v___x_4588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
lean_ctor_set(v___x_4588_, 1, v_b_4571_);
v_sz_4589_ = lean_array_size(v_cs_4583_);
v___x_4590_ = ((size_t)0ULL);
v___x_4591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_inh_4569_, v_cs_4583_, v_sz_4589_, v___x_4590_, v___x_4588_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec_ref(v_cs_4583_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4608_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4608_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4608_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v_fst_4596_; 
v_fst_4596_ = lean_ctor_get(v_a_4592_, 0);
if (lean_obj_tag(v_fst_4596_) == 0)
{
lean_object* v_snd_4597_; lean_object* v___x_4599_; 
v_snd_4597_ = lean_ctor_get(v_a_4592_, 1);
lean_inc(v_snd_4597_);
lean_dec(v_a_4592_);
if (v_isShared_4586_ == 0)
{
lean_ctor_set_tag(v___x_4585_, 1);
lean_ctor_set(v___x_4585_, 0, v_snd_4597_);
v___x_4599_ = v___x_4585_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_snd_4597_);
v___x_4599_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
lean_object* v___x_4601_; 
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v___x_4599_);
v___x_4601_ = v___x_4594_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
else
{
lean_object* v_val_4604_; lean_object* v___x_4606_; 
lean_inc_ref(v_fst_4596_);
lean_dec(v_a_4592_);
lean_del_object(v___x_4585_);
v_val_4604_ = lean_ctor_get(v_fst_4596_, 0);
lean_inc(v_val_4604_);
lean_dec_ref(v_fst_4596_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v_val_4604_);
v___x_4606_ = v___x_4594_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_val_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4616_; 
lean_del_object(v___x_4585_);
v_a_4609_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4611_ = v___x_4591_;
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4591_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4614_; 
if (v_isShared_4612_ == 0)
{
v___x_4614_ = v___x_4611_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_a_4609_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
}
}
else
{
lean_object* v_vs_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4652_; 
v_vs_4618_ = lean_ctor_get(v_n_4570_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v_n_4570_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4620_ = v_n_4570_;
v_isShared_4621_ = v_isSharedCheck_4652_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_vs_4618_);
lean_dec(v_n_4570_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4652_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; size_t v_sz_4624_; size_t v___x_4625_; lean_object* v___x_4626_; 
v___x_4622_ = lean_box(0);
v___x_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
lean_ctor_set(v___x_4623_, 1, v_b_4571_);
v_sz_4624_ = lean_array_size(v_vs_4618_);
v___x_4625_ = ((size_t)0ULL);
v___x_4626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_4618_, v_sz_4624_, v___x_4625_, v___x_4623_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec_ref(v_vs_4618_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4643_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4629_ = v___x_4626_;
v_isShared_4630_ = v_isSharedCheck_4643_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4626_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4643_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v_fst_4631_; 
v_fst_4631_ = lean_ctor_get(v_a_4627_, 0);
if (lean_obj_tag(v_fst_4631_) == 0)
{
lean_object* v_snd_4632_; lean_object* v___x_4634_; 
v_snd_4632_ = lean_ctor_get(v_a_4627_, 1);
lean_inc(v_snd_4632_);
lean_dec(v_a_4627_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 0, v_snd_4632_);
v___x_4634_ = v___x_4620_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_snd_4632_);
v___x_4634_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4636_; 
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v___x_4634_);
v___x_4636_ = v___x_4629_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
else
{
lean_object* v_val_4639_; lean_object* v___x_4641_; 
lean_inc_ref(v_fst_4631_);
lean_dec(v_a_4627_);
lean_del_object(v___x_4620_);
v_val_4639_ = lean_ctor_get(v_fst_4631_, 0);
lean_inc(v_val_4639_);
lean_dec_ref(v_fst_4631_);
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v_val_4639_);
v___x_4641_ = v___x_4629_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_val_4639_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_del_object(v___x_4620_);
v_a_4644_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4626_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4626_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_inh_4653_, lean_object* v_as_4654_, size_t v_sz_4655_, size_t v_i_4656_, lean_object* v_b_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
uint8_t v___x_4669_; 
v___x_4669_ = lean_usize_dec_lt(v_i_4656_, v_sz_4655_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4670_; 
v___x_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4670_, 0, v_b_4657_);
return v___x_4670_;
}
else
{
lean_object* v_snd_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4705_; 
v_snd_4671_ = lean_ctor_get(v_b_4657_, 1);
v_isSharedCheck_4705_ = !lean_is_exclusive(v_b_4657_);
if (v_isSharedCheck_4705_ == 0)
{
lean_object* v_unused_4706_; 
v_unused_4706_ = lean_ctor_get(v_b_4657_, 0);
lean_dec(v_unused_4706_);
v___x_4673_ = v_b_4657_;
v_isShared_4674_ = v_isSharedCheck_4705_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_snd_4671_);
lean_dec(v_b_4657_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4705_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v_a_4675_; lean_object* v___x_4676_; 
v_a_4675_ = lean_array_uget_borrowed(v_as_4654_, v_i_4656_);
lean_inc(v_snd_4671_);
lean_inc(v_a_4675_);
v___x_4676_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_inh_4653_, v_a_4675_, v_snd_4671_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4696_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4679_ = v___x_4676_;
v_isShared_4680_ = v_isSharedCheck_4696_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4676_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4696_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
if (lean_obj_tag(v_a_4677_) == 0)
{
lean_object* v___x_4681_; lean_object* v___x_4683_; 
v___x_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4681_, 0, v_a_4677_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4681_);
v___x_4683_ = v___x_4673_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4681_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v_snd_4671_);
v___x_4683_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4685_; 
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v___x_4683_);
v___x_4685_ = v___x_4679_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4683_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4689_; lean_object* v___x_4691_; 
lean_del_object(v___x_4679_);
lean_dec(v_snd_4671_);
v_a_4688_ = lean_ctor_get(v_a_4677_, 0);
lean_inc(v_a_4688_);
lean_dec_ref(v_a_4677_);
v___x_4689_ = lean_box(0);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 1, v_a_4688_);
lean_ctor_set(v___x_4673_, 0, v___x_4689_);
v___x_4691_ = v___x_4673_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4689_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v_a_4688_);
v___x_4691_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
size_t v___x_4692_; size_t v___x_4693_; 
v___x_4692_ = ((size_t)1ULL);
v___x_4693_ = lean_usize_add(v_i_4656_, v___x_4692_);
v_i_4656_ = v___x_4693_;
v_b_4657_ = v___x_4691_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_del_object(v___x_4673_);
lean_dec(v_snd_4671_);
v_a_4697_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4676_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4676_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object* v_inh_4707_, lean_object* v_as_4708_, lean_object* v_sz_4709_, lean_object* v_i_4710_, lean_object* v_b_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
size_t v_sz_boxed_4723_; size_t v_i_boxed_4724_; lean_object* v_res_4725_; 
v_sz_boxed_4723_ = lean_unbox_usize(v_sz_4709_);
lean_dec(v_sz_4709_);
v_i_boxed_4724_ = lean_unbox_usize(v_i_4710_);
lean_dec(v_i_4710_);
v_res_4725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_inh_4707_, v_as_4708_, v_sz_boxed_4723_, v_i_boxed_4724_, v_b_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v_as_4708_);
lean_dec(v_inh_4707_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_inh_4726_, lean_object* v_n_4727_, lean_object* v_b_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_inh_4726_, v_n_4727_, v_b_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec(v_inh_4726_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_4741_, size_t v_sz_4742_, size_t v_i_4743_, lean_object* v_b_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
uint8_t v___x_4756_; 
v___x_4756_ = lean_usize_dec_lt(v_i_4743_, v_sz_4742_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4757_; 
v___x_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4757_, 0, v_b_4744_);
return v___x_4757_;
}
else
{
lean_object* v_snd_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4782_; 
v_snd_4758_ = lean_ctor_get(v_b_4744_, 1);
v_isSharedCheck_4782_ = !lean_is_exclusive(v_b_4744_);
if (v_isSharedCheck_4782_ == 0)
{
lean_object* v_unused_4783_; 
v_unused_4783_ = lean_ctor_get(v_b_4744_, 0);
lean_dec(v_unused_4783_);
v___x_4760_ = v_b_4744_;
v_isShared_4761_ = v_isSharedCheck_4782_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_snd_4758_);
lean_dec(v_b_4744_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4782_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v_a_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_a_4762_ = lean_array_uget_borrowed(v_as_4741_, v_i_4743_);
v___x_4763_ = lean_box(0);
lean_inc(v_a_4762_);
v___x_4764_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4758_, v_a_4762_, v___x_4763_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
lean_dec_ref(v___x_4764_);
v___x_4765_ = lean_box(0);
v___x_4766_ = lean_unsigned_to_nat(1u);
v___x_4767_ = lean_nat_add(v_snd_4758_, v___x_4766_);
lean_dec(v_snd_4758_);
if (v_isShared_4761_ == 0)
{
lean_ctor_set(v___x_4760_, 1, v___x_4767_);
lean_ctor_set(v___x_4760_, 0, v___x_4765_);
v___x_4769_ = v___x_4760_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4765_);
lean_ctor_set(v_reuseFailAlloc_4773_, 1, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
size_t v___x_4770_; size_t v___x_4771_; 
v___x_4770_ = ((size_t)1ULL);
v___x_4771_ = lean_usize_add(v_i_4743_, v___x_4770_);
v_i_4743_ = v___x_4771_;
v_b_4744_ = v___x_4769_;
goto _start;
}
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
lean_del_object(v___x_4760_);
lean_dec(v_snd_4758_);
v_a_4774_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4764_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4764_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_4784_, lean_object* v_sz_4785_, lean_object* v_i_4786_, lean_object* v_b_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
size_t v_sz_boxed_4799_; size_t v_i_boxed_4800_; lean_object* v_res_4801_; 
v_sz_boxed_4799_ = lean_unbox_usize(v_sz_4785_);
lean_dec(v_sz_4785_);
v_i_boxed_4800_ = lean_unbox_usize(v_i_4786_);
lean_dec(v_i_4786_);
v_res_4801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4784_, v_sz_boxed_4799_, v_i_boxed_4800_, v_b_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
lean_dec(v___y_4791_);
lean_dec_ref(v___y_4790_);
lean_dec(v___y_4789_);
lean_dec(v___y_4788_);
lean_dec_ref(v_as_4784_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_4802_, size_t v_sz_4803_, size_t v_i_4804_, lean_object* v_b_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
uint8_t v___x_4817_; 
v___x_4817_ = lean_usize_dec_lt(v_i_4804_, v_sz_4803_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4818_; 
v___x_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4818_, 0, v_b_4805_);
return v___x_4818_;
}
else
{
lean_object* v_snd_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4843_; 
v_snd_4819_ = lean_ctor_get(v_b_4805_, 1);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_b_4805_);
if (v_isSharedCheck_4843_ == 0)
{
lean_object* v_unused_4844_; 
v_unused_4844_ = lean_ctor_get(v_b_4805_, 0);
lean_dec(v_unused_4844_);
v___x_4821_ = v_b_4805_;
v_isShared_4822_ = v_isSharedCheck_4843_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_snd_4819_);
lean_dec(v_b_4805_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4843_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v_a_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v_a_4823_ = lean_array_uget_borrowed(v_as_4802_, v_i_4804_);
v___x_4824_ = lean_box(0);
lean_inc(v_a_4823_);
v___x_4825_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4819_, v_a_4823_, v___x_4824_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4830_; 
lean_dec_ref(v___x_4825_);
v___x_4826_ = lean_box(0);
v___x_4827_ = lean_unsigned_to_nat(1u);
v___x_4828_ = lean_nat_add(v_snd_4819_, v___x_4827_);
lean_dec(v_snd_4819_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 1, v___x_4828_);
lean_ctor_set(v___x_4821_, 0, v___x_4826_);
v___x_4830_ = v___x_4821_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
size_t v___x_4831_; size_t v___x_4832_; lean_object* v___x_4833_; 
v___x_4831_ = ((size_t)1ULL);
v___x_4832_ = lean_usize_add(v_i_4804_, v___x_4831_);
v___x_4833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4802_, v_sz_4803_, v___x_4832_, v___x_4830_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
return v___x_4833_;
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
lean_del_object(v___x_4821_);
lean_dec(v_snd_4819_);
v_a_4835_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4825_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4825_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_4845_, lean_object* v_sz_4846_, lean_object* v_i_4847_, lean_object* v_b_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
size_t v_sz_boxed_4860_; size_t v_i_boxed_4861_; lean_object* v_res_4862_; 
v_sz_boxed_4860_ = lean_unbox_usize(v_sz_4846_);
lean_dec(v_sz_4846_);
v_i_boxed_4861_ = lean_unbox_usize(v_i_4847_);
lean_dec(v_i_4847_);
v_res_4862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_as_4845_, v_sz_boxed_4860_, v_i_boxed_4861_, v_b_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec(v___y_4850_);
lean_dec(v___y_4849_);
lean_dec_ref(v_as_4845_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(lean_object* v_t_4863_, lean_object* v_init_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v_root_4876_; lean_object* v_tail_4877_; lean_object* v___x_4878_; 
v_root_4876_ = lean_ctor_get(v_t_4863_, 0);
lean_inc_ref(v_root_4876_);
v_tail_4877_ = lean_ctor_get(v_t_4863_, 1);
lean_inc_ref(v_tail_4877_);
lean_dec_ref(v_t_4863_);
lean_inc(v_init_4864_);
v___x_4878_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4864_, v_root_4876_, v_init_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
lean_dec(v_init_4864_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4915_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4881_ = v___x_4878_;
v_isShared_4882_ = v_isSharedCheck_4915_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4878_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4915_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
if (lean_obj_tag(v_a_4879_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4885_; 
lean_dec_ref(v_tail_4877_);
v_a_4883_ = lean_ctor_get(v_a_4879_, 0);
lean_inc(v_a_4883_);
lean_dec_ref(v_a_4879_);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 0, v_a_4883_);
v___x_4885_ = v___x_4881_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4883_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; size_t v_sz_4890_; size_t v___x_4891_; lean_object* v___x_4892_; 
lean_del_object(v___x_4881_);
v_a_4887_ = lean_ctor_get(v_a_4879_, 0);
lean_inc(v_a_4887_);
lean_dec_ref(v_a_4879_);
v___x_4888_ = lean_box(0);
v___x_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4888_);
lean_ctor_set(v___x_4889_, 1, v_a_4887_);
v_sz_4890_ = lean_array_size(v_tail_4877_);
v___x_4891_ = ((size_t)0ULL);
v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_tail_4877_, v_sz_4890_, v___x_4891_, v___x_4889_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
lean_dec_ref(v_tail_4877_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4906_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4895_ = v___x_4892_;
v_isShared_4896_ = v_isSharedCheck_4906_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4892_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4906_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v_fst_4897_; 
v_fst_4897_ = lean_ctor_get(v_a_4893_, 0);
if (lean_obj_tag(v_fst_4897_) == 0)
{
lean_object* v_snd_4898_; lean_object* v___x_4900_; 
v_snd_4898_ = lean_ctor_get(v_a_4893_, 1);
lean_inc(v_snd_4898_);
lean_dec(v_a_4893_);
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 0, v_snd_4898_);
v___x_4900_ = v___x_4895_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_snd_4898_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
else
{
lean_object* v_val_4902_; lean_object* v___x_4904_; 
lean_inc_ref(v_fst_4897_);
lean_dec(v_a_4893_);
v_val_4902_ = lean_ctor_get(v_fst_4897_, 0);
lean_inc(v_val_4902_);
lean_dec_ref(v_fst_4897_);
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 0, v_val_4902_);
v___x_4904_ = v___x_4895_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_val_4902_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
else
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4914_; 
v_a_4907_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4909_ = v___x_4892_;
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4892_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
if (v_isShared_4910_ == 0)
{
v___x_4912_ = v___x_4909_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4907_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_dec_ref(v_tail_4877_);
v_a_4916_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4878_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4878_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_4924_, lean_object* v_init_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_t_4924_, v_init_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec(v___y_4927_);
lean_dec(v___y_4926_);
return v_res_4937_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4940_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1));
v___x_4941_ = lean_unsigned_to_nat(2u);
v___x_4942_ = lean_unsigned_to_nat(103u);
v___x_4943_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0));
v___x_4944_ = ((lean_object*)(l_Int_Linear_Poly_checkNoElimVars___closed__0));
v___x_4945_ = l_mkPanicMessageWithDecl(v___x_4944_, v___x_4943_, v___x_4942_, v___x_4941_, v___x_4940_);
return v___x_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4946_, v_a_4954_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v_vars_4959_; lean_object* v_diseqs_4960_; lean_object* v_size_4961_; lean_object* v_size_4962_; uint8_t v___x_4963_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref(v___x_4957_);
v_vars_4959_ = lean_ctor_get(v_a_4958_, 0);
lean_inc_ref(v_vars_4959_);
v_diseqs_4960_ = lean_ctor_get(v_a_4958_, 9);
lean_inc_ref(v_diseqs_4960_);
lean_dec(v_a_4958_);
v_size_4961_ = lean_ctor_get(v_vars_4959_, 2);
lean_inc(v_size_4961_);
lean_dec_ref(v_vars_4959_);
v_size_4962_ = lean_ctor_get(v_diseqs_4960_, 2);
v___x_4963_ = lean_nat_dec_eq(v_size_4961_, v_size_4962_);
lean_dec(v_size_4961_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; lean_object* v___x_4965_; 
lean_dec_ref(v_diseqs_4960_);
v___x_4964_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2);
v___x_4965_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(v___x_4964_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_);
return v___x_4965_;
}
else
{
lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4966_ = lean_unsigned_to_nat(0u);
v___x_4967_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_diseqs_4960_, v___x_4966_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4975_; 
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4975_ == 0)
{
lean_object* v_unused_4976_; 
v_unused_4976_ = lean_ctor_get(v___x_4967_, 0);
lean_dec(v_unused_4976_);
v___x_4969_ = v___x_4967_;
v_isShared_4970_ = v_isSharedCheck_4975_;
goto v_resetjp_4968_;
}
else
{
lean_dec(v___x_4967_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4975_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4971_ = lean_box(0);
if (v_isShared_4970_ == 0)
{
lean_ctor_set(v___x_4969_, 0, v___x_4971_);
v___x_4973_ = v___x_4969_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4971_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
v_a_4977_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4967_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4967_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
}
else
{
lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4992_; 
v_a_4985_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4987_ = v___x_4957_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4957_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4990_; 
if (v_isShared_4988_ == 0)
{
v___x_4990_ = v___x_4987_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___boxed(lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
lean_dec(v_a_5002_);
lean_dec_ref(v_a_5001_);
lean_dec(v_a_5000_);
lean_dec_ref(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
lean_dec(v_a_4996_);
lean_dec_ref(v_a_4995_);
lean_dec(v_a_4994_);
lean_dec(v_a_4993_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v___x_5017_; 
lean_dec_ref(v___x_5016_);
v___x_5017_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v___x_5018_; 
lean_dec_ref(v___x_5017_);
v___x_5018_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v___x_5019_; 
lean_dec_ref(v___x_5018_);
v___x_5019_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v___x_5020_; 
lean_dec_ref(v___x_5019_);
v___x_5020_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v___x_5021_; 
lean_dec_ref(v___x_5020_);
v___x_5021_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v___x_5022_; 
lean_dec_ref(v___x_5021_);
v___x_5022_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5022_;
}
else
{
return v___x_5021_;
}
}
else
{
return v___x_5020_;
}
}
else
{
return v___x_5019_;
}
}
else
{
return v___x_5018_;
}
}
else
{
return v___x_5017_;
}
}
else
{
return v___x_5016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
lean_dec(v_a_5032_);
lean_dec_ref(v_a_5031_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
lean_dec(v_a_5024_);
lean_dec(v_a_5023_);
return v_res_5034_;
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
