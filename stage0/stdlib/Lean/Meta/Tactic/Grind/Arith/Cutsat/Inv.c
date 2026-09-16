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
uint8_t l_Int_Internal_Linear_Poly_isSorted(lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_once_cell_t l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_checkCoeffs___closed__0;
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_checkCoeffs(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCoeffs___boxed(lean_object*);
static lean_once_cell_t l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv"};
static const lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0 = (const lean_object*)&l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0_value;
static const lean_string_object l_Int_Internal_Linear_Poly_checkNoElimVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Int.Internal.Linear.Poly.checkNoElimVars"};
static const lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars___closed__1 = (const lean_object*)&l_Int_Internal_Linear_Poly_checkNoElimVars___closed__1_value;
static const lean_string_object l_Int_Internal_Linear_Poly_checkNoElimVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 111, .m_capacity = 111, .m_length = 110, .m_data = "assertion violation: !( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv.3889168869._hygCtx._hyg.33.0 )\n  "};
static const lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars___closed__2 = (const lean_object*)&l_Int_Internal_Linear_Poly_checkNoElimVars___closed__2_value;
static lean_once_cell_t l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv.0.Int.Internal.Linear.Poly.checkOccs.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 122, .m_capacity = 122, .m_length = 121, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv.990649928._hygCtx._hyg.65.0 ).contains y\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Int.Internal.Linear.Poly.checkCnstrOf"};
static const lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0 = (const lean_object*)&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0_value;
static const lean_string_object l_Int_Internal_Linear_Poly_checkCnstrOf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "assertion violation: x == y\n\n"};
static const lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__1 = (const lean_object*)&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__1_value;
static lean_once_cell_t l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2;
static const lean_string_object l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3 = (const lean_object*)&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3_value;
static lean_once_cell_t l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4;
static const lean_string_object l_Int_Internal_Linear_Poly_checkCnstrOf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: p.isSorted\n  "};
static const lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__5 = (const lean_object*)&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__5_value;
static lean_once_cell_t l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6;
static const lean_string_object l_Int_Internal_Linear_Poly_checkCnstrOf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: p.checkCoeffs\n  "};
static const lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__7 = (const lean_object*)&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__7_value;
static lean_once_cell_t l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_checkCoeffs(lean_object* v_x_3_){
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
v___x_7_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCoeffs___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_x_11_);
lean_dec_ref(v_x_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
static lean_object* _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(lean_object* v_msg_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_1389__overap_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_1389__overap_28_ = lean_panic_fn_borrowed(v___x_27_, v_msg_15_);
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
v___x_29_ = lean_apply_11(v___x_1389__overap_28_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, lean_box(0));
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___boxed(lean_object* v_msg_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v_msg_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
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
static lean_object* _init_l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__2));
v___x_47_ = lean_unsigned_to_nat(2u);
v___x_48_ = lean_unsigned_to_nat(23u);
v___x_49_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__1));
v___x_50_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_51_ = l_mkPanicMessageWithDecl(v___x_50_, v___x_49_, v___x_48_, v___x_47_, v___x_46_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars(lean_object* v_p_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
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
lean_dec_ref_known(v___x_66_, 1);
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
v___x_70_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3, &l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3_once, _init_l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3);
v___x_71_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_70_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars___boxed(lean_object* v_p_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Int_Internal_Linear_Poly_checkNoElimVars(v_p_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(lean_object* v_k_95_, lean_object* v_t_96_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg___boxed(lean_object* v_k_105_, lean_object* v_t_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_105_, v_t_106_);
lean_dec(v_t_106_);
lean_dec(v_k_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__1));
v___x_112_ = lean_unsigned_to_nat(4u);
v___x_113_ = lean_unsigned_to_nat(30u);
v___x_114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__0));
v___x_115_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_116_ = l_mkPanicMessageWithDecl(v___x_115_, v___x_114_, v___x_113_, v___x_112_, v___x_111_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(lean_object* v_y_117_, lean_object* v_p_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
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
lean_dec_ref_known(v___x_132_, 1);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_y_117_, v_a_133_);
lean_dec(v_a_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2);
v___x_136_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_135_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___boxed(lean_object* v_y_148_, lean_object* v_p_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(v_y_148_, v_p_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0(lean_object* v_00_u03b2_162_, lean_object* v_k_163_, lean_object* v_t_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_163_, v_t_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___boxed(lean_object* v_00_u03b2_166_, lean_object* v_k_167_, lean_object* v_t_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0(v_00_u03b2_166_, v_k_167_, v_t_168_);
lean_dec(v_t_168_);
lean_dec(v_k_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkOccs(lean_object* v_p_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
if (lean_obj_tag(v_p_171_) == 1)
{
lean_object* v_v_183_; lean_object* v_p_184_; lean_object* v___x_185_; 
v_v_183_ = lean_ctor_get(v_p_171_, 1);
v_p_184_ = lean_ctor_get(v_p_171_, 2);
v___x_185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(v_v_183_, v_p_184_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkOccs___boxed(lean_object* v_p_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Int_Internal_Linear_Poly_checkOccs(v_p_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
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
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_203_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__1));
v___x_204_ = lean_unsigned_to_nat(2u);
v___x_205_ = lean_unsigned_to_nat(41u);
v___x_206_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_207_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_208_ = l_mkPanicMessageWithDecl(v___x_207_, v___x_206_, v___x_205_, v___x_204_, v___x_203_);
return v___x_208_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_211_ = lean_unsigned_to_nat(24u);
v___x_212_ = lean_unsigned_to_nat(40u);
v___x_213_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_214_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_215_ = l_mkPanicMessageWithDecl(v___x_214_, v___x_213_, v___x_212_, v___x_211_, v___x_210_);
return v___x_215_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__5));
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_unsigned_to_nat(35u);
v___x_220_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_221_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_222_ = l_mkPanicMessageWithDecl(v___x_221_, v___x_220_, v___x_219_, v___x_218_, v___x_217_);
return v___x_222_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__7));
v___x_225_ = lean_unsigned_to_nat(2u);
v___x_226_ = lean_unsigned_to_nat(36u);
v___x_227_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_228_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_229_ = l_mkPanicMessageWithDecl(v___x_228_, v___x_227_, v___x_226_, v___x_225_, v___x_224_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf(lean_object* v_p_230_, lean_object* v_x_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; uint8_t v___x_262_; 
v___x_262_ = l_Int_Internal_Linear_Poly_isSorted(v_p_230_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6);
v___x_264_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_263_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
return v___x_264_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_230_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8);
v___x_267_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_266_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
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
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = lean_unbox(v_a_269_);
lean_dec(v_a_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = l_Int_Internal_Linear_Poly_checkNoElimVars(v_p_230_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_272_; 
lean_dec_ref_known(v___x_271_, 1);
v___x_272_ = l_Int_Internal_Linear_Poly_checkOccs(v_p_230_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_dec_ref_known(v___x_272_, 1);
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
v___x_256_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2);
v___x_257_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_256_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
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
v___x_260_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4);
v___x_261_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_260_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___boxed(lean_object* v_p_281_, lean_object* v_x_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_281_, v_x_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
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
lean_object* v___x_308_; lean_object* v___x_3860__overap_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0);
v___x_3860__overap_309_ = lean_panic_fn_borrowed(v___x_308_, v_msg_296_);
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
v___x_310_ = lean_apply_11(v___x_3860__overap_309_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, lean_box(0));
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
v___x_330_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_331_ = l_mkPanicMessageWithDecl(v___x_330_, v___x_329_, v___x_328_, v___x_327_, v___x_326_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_332_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_333_ = lean_unsigned_to_nat(30u);
v___x_334_ = lean_unsigned_to_nat(48u);
v___x_335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_336_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
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
lean_object* v_snd_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_432_; 
v_snd_357_ = lean_ctor_get(v_b_343_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_b_343_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v_b_343_, 0);
lean_dec(v_unused_433_);
v___x_359_ = v_b_343_;
v_isShared_360_ = v_isSharedCheck_432_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snd_357_);
lean_dec(v_b_343_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_432_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_a_361_; lean_object* v_p_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_430_; 
v_a_361_ = lean_array_uget(v_as_340_, v_i_342_);
v_p_362_ = lean_ctor_get(v_a_361_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_a_361_, 1);
lean_dec(v_unused_431_);
v___x_364_ = v_a_361_;
v_isShared_365_ = v_isSharedCheck_430_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_p_362_);
lean_dec(v_a_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_430_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; 
v___x_366_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_362_, v_____s_338_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_367_; lean_object* v_a_369_; lean_object* v___x_376_; uint8_t v___y_378_; 
lean_dec_ref_known(v___x_366_, 1);
v___x_367_ = lean_box(0);
v___x_376_ = lean_box(0);
if (lean_obj_tag(v_p_362_) == 1)
{
lean_object* v_k_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_k_409_ = lean_ctor_get(v_p_362_, 0);
lean_inc(v_k_409_);
lean_dec_ref_known(v_p_362_, 3);
v___x_410_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_411_ = lean_int_dec_lt(v_k_409_, v___x_410_);
lean_dec(v_k_409_);
if (v___x_411_ == 0)
{
if (v_isLower_339_ == 0)
{
v___y_378_ = v___x_355_;
goto v___jp_377_;
}
else
{
v___y_378_ = v___x_411_;
goto v___jp_377_;
}
}
else
{
v___y_378_ = v_isLower_339_;
goto v___jp_377_;
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_del_object(v___x_364_);
lean_dec_ref(v_p_362_);
lean_dec(v_snd_357_);
v___x_412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_413_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_412_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_dec_ref_known(v___x_413_, 1);
v_a_369_ = v___x_376_;
goto v___jp_368_;
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_del_object(v___x_359_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
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
v___jp_377_:
{
if (v___y_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_380_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_379_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_400_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_400_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_400_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_400_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
if (lean_obj_tag(v_a_381_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_398_; 
lean_del_object(v___x_359_);
v_a_385_ = lean_ctor_get(v_a_381_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_a_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_387_ = v_a_381_;
v_isShared_388_ = v_isSharedCheck_398_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v_a_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_398_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set_tag(v___x_387_, 1);
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_397_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_snd_357_);
lean_ctor_set(v___x_364_, 0, v___x_390_);
v___x_392_ = v___x_364_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_snd_357_);
v___x_392_ = v_reuseFailAlloc_396_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_392_);
v___x_394_ = v___x_383_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
else
{
lean_object* v_a_399_; 
lean_del_object(v___x_383_);
lean_del_object(v___x_364_);
lean_dec(v_snd_357_);
v_a_399_ = lean_ctor_get(v_a_381_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v_a_381_, 1);
v_a_369_ = v_a_399_;
goto v___jp_368_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_del_object(v___x_364_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
v_a_401_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_380_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_380_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_del_object(v___x_364_);
lean_dec(v_snd_357_);
v_a_369_ = v___x_376_;
goto v___jp_368_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_del_object(v___x_364_);
lean_dec_ref(v_p_362_);
lean_del_object(v___x_359_);
lean_dec(v_snd_357_);
v_a_422_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_366_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_366_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_____s_434_ = _args[0];
lean_object* v_isLower_435_ = _args[1];
lean_object* v_as_436_ = _args[2];
lean_object* v_sz_437_ = _args[3];
lean_object* v_i_438_ = _args[4];
lean_object* v_b_439_ = _args[5];
lean_object* v___y_440_ = _args[6];
lean_object* v___y_441_ = _args[7];
lean_object* v___y_442_ = _args[8];
lean_object* v___y_443_ = _args[9];
lean_object* v___y_444_ = _args[10];
lean_object* v___y_445_ = _args[11];
lean_object* v___y_446_ = _args[12];
lean_object* v___y_447_ = _args[13];
lean_object* v___y_448_ = _args[14];
lean_object* v___y_449_ = _args[15];
lean_object* v___y_450_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_451_; size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_isLower_boxed_451_ = lean_unbox(v_isLower_435_);
v_sz_boxed_452_ = lean_unbox_usize(v_sz_437_);
lean_dec(v_sz_437_);
v_i_boxed_453_ = lean_unbox_usize(v_i_438_);
lean_dec(v_i_438_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_434_, v_isLower_boxed_451_, v_as_436_, v_sz_boxed_452_, v_i_boxed_453_, v_b_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v_as_436_);
lean_dec(v_____s_434_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(lean_object* v_____s_455_, uint8_t v_isLower_456_, lean_object* v_as_457_, size_t v_sz_458_, size_t v_i_459_, lean_object* v_b_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = lean_usize_dec_lt(v_i_459_, v_sz_458_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v_b_460_);
return v___x_473_;
}
else
{
lean_object* v_snd_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_549_; 
v_snd_474_ = lean_ctor_get(v_b_460_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_b_460_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v_b_460_, 0);
lean_dec(v_unused_550_);
v___x_476_ = v_b_460_;
v_isShared_477_ = v_isSharedCheck_549_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snd_474_);
lean_dec(v_b_460_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_549_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_a_478_; lean_object* v_p_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_547_; 
v_a_478_ = lean_array_uget(v_as_457_, v_i_459_);
v_p_479_ = lean_ctor_get(v_a_478_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_a_478_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v_a_478_, 1);
lean_dec(v_unused_548_);
v___x_481_ = v_a_478_;
v_isShared_482_ = v_isSharedCheck_547_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_p_479_);
lean_dec(v_a_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_547_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; 
v___x_483_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_479_, v_____s_455_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v_a_487_; uint8_t v___y_495_; 
lean_dec_ref_known(v___x_483_, 1);
v___x_484_ = lean_box(0);
v___x_485_ = lean_box(0);
if (lean_obj_tag(v_p_479_) == 1)
{
lean_object* v_k_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_k_526_ = lean_ctor_get(v_p_479_, 0);
lean_inc(v_k_526_);
lean_dec_ref_known(v_p_479_, 3);
v___x_527_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_528_ = lean_int_dec_lt(v_k_526_, v___x_527_);
lean_dec(v_k_526_);
if (v___x_528_ == 0)
{
if (v_isLower_456_ == 0)
{
v___y_495_ = v___x_472_;
goto v___jp_494_;
}
else
{
v___y_495_ = v___x_528_;
goto v___jp_494_;
}
}
else
{
v___y_495_ = v_isLower_456_;
goto v___jp_494_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_del_object(v___x_481_);
lean_dec_ref(v_p_479_);
lean_dec(v_snd_474_);
v___x_529_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_530_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_529_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_dec_ref_known(v___x_530_, 1);
v_a_487_ = v___x_484_;
goto v___jp_486_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_476_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
v___jp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v_a_487_);
lean_ctor_set(v___x_476_, 0, v___x_485_);
v___x_489_ = v___x_476_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_a_487_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_459_, v___x_490_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_455_, v_isLower_456_, v_as_457_, v_sz_458_, v___x_491_, v___x_489_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v___x_492_;
}
}
v___jp_494_:
{
if (v___y_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_497_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_496_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
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
lean_del_object(v___x_476_);
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
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v_snd_474_);
lean_ctor_set(v___x_481_, 0, v___x_507_);
v___x_509_ = v___x_481_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_snd_474_);
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
lean_del_object(v___x_481_);
lean_dec(v_snd_474_);
v_a_516_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v_a_498_, 1);
v_a_487_ = v_a_516_;
goto v___jp_486_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_del_object(v___x_481_);
lean_del_object(v___x_476_);
lean_dec(v_snd_474_);
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
else
{
lean_del_object(v___x_481_);
lean_dec(v_snd_474_);
v_a_487_ = v___x_484_;
goto v___jp_486_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_481_);
lean_dec_ref(v_p_479_);
lean_del_object(v___x_476_);
lean_dec(v_snd_474_);
v_a_539_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_483_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_483_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_551_ = _args[0];
lean_object* v_isLower_552_ = _args[1];
lean_object* v_as_553_ = _args[2];
lean_object* v_sz_554_ = _args[3];
lean_object* v_i_555_ = _args[4];
lean_object* v_b_556_ = _args[5];
lean_object* v___y_557_ = _args[6];
lean_object* v___y_558_ = _args[7];
lean_object* v___y_559_ = _args[8];
lean_object* v___y_560_ = _args[9];
lean_object* v___y_561_ = _args[10];
lean_object* v___y_562_ = _args[11];
lean_object* v___y_563_ = _args[12];
lean_object* v___y_564_ = _args[13];
lean_object* v___y_565_ = _args[14];
lean_object* v___y_566_ = _args[15];
lean_object* v___y_567_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_568_; size_t v_sz_boxed_569_; size_t v_i_boxed_570_; lean_object* v_res_571_; 
v_isLower_boxed_568_ = lean_unbox(v_isLower_552_);
v_sz_boxed_569_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_570_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_551_, v_isLower_boxed_568_, v_as_553_, v_sz_boxed_569_, v_i_boxed_570_, v_b_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v_as_553_);
lean_dec(v_____s_551_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object* v_____s_572_, uint8_t v_isLower_573_, lean_object* v_as_574_, size_t v_sz_575_, size_t v_i_576_, lean_object* v_b_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_lt(v_i_576_, v_sz_575_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v_b_577_);
return v___x_590_;
}
else
{
lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_659_; 
v_snd_591_ = lean_ctor_get(v_b_577_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_b_577_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_b_577_, 0);
lean_dec(v_unused_660_);
v___x_593_ = v_b_577_;
v_isShared_594_ = v_isSharedCheck_659_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_dec(v_b_577_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_659_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_a_595_; lean_object* v_p_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_657_; 
v_a_595_ = lean_array_uget(v_as_574_, v_i_576_);
v_p_596_ = lean_ctor_get(v_a_595_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_a_595_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v_a_595_, 1);
lean_dec(v_unused_658_);
v___x_598_ = v_a_595_;
v_isShared_599_ = v_isSharedCheck_657_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_p_596_);
lean_dec(v_a_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_657_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; 
v___x_600_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_596_, v_____s_572_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v___x_601_; lean_object* v_a_603_; lean_object* v___x_610_; uint8_t v___y_612_; 
lean_dec_ref_known(v___x_600_, 1);
v___x_601_ = lean_box(0);
v___x_610_ = lean_box(0);
if (lean_obj_tag(v_p_596_) == 1)
{
lean_object* v_k_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_k_636_ = lean_ctor_get(v_p_596_, 0);
lean_inc(v_k_636_);
lean_dec_ref_known(v_p_596_, 3);
v___x_637_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_638_ = lean_int_dec_lt(v_k_636_, v___x_637_);
lean_dec(v_k_636_);
if (v___x_638_ == 0)
{
if (v_isLower_573_ == 0)
{
v___y_612_ = v___x_589_;
goto v___jp_611_;
}
else
{
v___y_612_ = v___x_638_;
goto v___jp_611_;
}
}
else
{
v___y_612_ = v_isLower_573_;
goto v___jp_611_;
}
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_del_object(v___x_598_);
lean_dec_ref(v_p_596_);
lean_dec(v_snd_591_);
v___x_639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_640_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_639_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec_ref_known(v___x_640_, 1);
v_a_603_ = v___x_610_;
goto v___jp_602_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_del_object(v___x_593_);
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
v___jp_602_:
{
lean_object* v___x_605_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_a_603_);
lean_ctor_set(v___x_593_, 0, v___x_601_);
v___x_605_ = v___x_593_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_a_603_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
size_t v___x_606_; size_t v___x_607_; 
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_576_, v___x_606_);
v_i_576_ = v___x_607_;
v_b_577_ = v___x_605_;
goto _start;
}
}
v___jp_611_:
{
if (v___y_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_614_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_613_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
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
lean_del_object(v___x_593_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v_a_615_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_snd_591_);
lean_ctor_set(v___x_598_, 0, v___x_619_);
v___x_621_ = v___x_598_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_snd_591_);
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
lean_del_object(v___x_598_);
lean_dec(v_snd_591_);
v_a_626_ = lean_ctor_get(v_a_615_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v_a_615_, 1);
v_a_603_ = v_a_626_;
goto v___jp_602_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_del_object(v___x_598_);
lean_del_object(v___x_593_);
lean_dec(v_snd_591_);
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
else
{
lean_del_object(v___x_598_);
lean_dec(v_snd_591_);
v_a_603_ = v___x_610_;
goto v___jp_602_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_del_object(v___x_598_);
lean_dec_ref(v_p_596_);
lean_del_object(v___x_593_);
lean_dec(v_snd_591_);
v_a_649_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_600_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_600_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_____s_661_ = _args[0];
lean_object* v_isLower_662_ = _args[1];
lean_object* v_as_663_ = _args[2];
lean_object* v_sz_664_ = _args[3];
lean_object* v_i_665_ = _args[4];
lean_object* v_b_666_ = _args[5];
lean_object* v___y_667_ = _args[6];
lean_object* v___y_668_ = _args[7];
lean_object* v___y_669_ = _args[8];
lean_object* v___y_670_ = _args[9];
lean_object* v___y_671_ = _args[10];
lean_object* v___y_672_ = _args[11];
lean_object* v___y_673_ = _args[12];
lean_object* v___y_674_ = _args[13];
lean_object* v___y_675_ = _args[14];
lean_object* v___y_676_ = _args[15];
lean_object* v___y_677_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_678_; size_t v_sz_boxed_679_; size_t v_i_boxed_680_; lean_object* v_res_681_; 
v_isLower_boxed_678_ = lean_unbox(v_isLower_662_);
v_sz_boxed_679_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v_i_boxed_680_ = lean_unbox_usize(v_i_665_);
lean_dec(v_i_665_);
v_res_681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_661_, v_isLower_boxed_678_, v_as_663_, v_sz_boxed_679_, v_i_boxed_680_, v_b_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v_as_663_);
lean_dec(v_____s_661_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object* v_____s_682_, uint8_t v_isLower_683_, lean_object* v_as_684_, size_t v_sz_685_, size_t v_i_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = lean_usize_dec_lt(v_i_686_, v_sz_685_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v_b_687_);
return v___x_700_;
}
else
{
lean_object* v_snd_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_769_; 
v_snd_701_ = lean_ctor_get(v_b_687_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_b_687_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v_b_687_, 0);
lean_dec(v_unused_770_);
v___x_703_ = v_b_687_;
v_isShared_704_ = v_isSharedCheck_769_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snd_701_);
lean_dec(v_b_687_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_769_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_a_705_; lean_object* v_p_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_767_; 
v_a_705_ = lean_array_uget(v_as_684_, v_i_686_);
v_p_706_ = lean_ctor_get(v_a_705_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_a_705_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v_a_705_, 1);
lean_dec(v_unused_768_);
v___x_708_ = v_a_705_;
v_isShared_709_ = v_isSharedCheck_767_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_p_706_);
lean_dec(v_a_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_767_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; 
v___x_710_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_706_, v_____s_682_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_a_714_; uint8_t v___y_722_; 
lean_dec_ref_known(v___x_710_, 1);
v___x_711_ = lean_box(0);
v___x_712_ = lean_box(0);
if (lean_obj_tag(v_p_706_) == 1)
{
lean_object* v_k_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_k_746_ = lean_ctor_get(v_p_706_, 0);
lean_inc(v_k_746_);
lean_dec_ref_known(v_p_706_, 3);
v___x_747_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_748_ = lean_int_dec_lt(v_k_746_, v___x_747_);
lean_dec(v_k_746_);
if (v___x_748_ == 0)
{
if (v_isLower_683_ == 0)
{
v___y_722_ = v___x_699_;
goto v___jp_721_;
}
else
{
v___y_722_ = v___x_748_;
goto v___jp_721_;
}
}
else
{
v___y_722_ = v_isLower_683_;
goto v___jp_721_;
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_del_object(v___x_708_);
lean_dec_ref(v_p_706_);
lean_dec(v_snd_701_);
v___x_749_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_750_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_749_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_dec_ref_known(v___x_750_, 1);
v_a_714_ = v___x_711_;
goto v___jp_713_;
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_del_object(v___x_703_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
v___jp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_a_714_);
lean_ctor_set(v___x_703_, 0, v___x_712_);
v___x_716_ = v___x_703_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_a_714_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; 
v___x_717_ = ((size_t)1ULL);
v___x_718_ = lean_usize_add(v_i_686_, v___x_717_);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_682_, v_isLower_683_, v_as_684_, v_sz_685_, v___x_718_, v___x_716_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v___x_719_;
}
}
v___jp_721_:
{
if (v___y_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_724_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_723_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_737_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_737_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_737_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_737_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
if (lean_obj_tag(v_a_725_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_731_; 
lean_del_object(v___x_703_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v_a_725_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_snd_701_);
lean_ctor_set(v___x_708_, 0, v___x_729_);
v___x_731_ = v___x_708_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_snd_701_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_731_);
v___x_733_ = v___x_727_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_object* v_a_736_; 
lean_del_object(v___x_727_);
lean_del_object(v___x_708_);
lean_dec(v_snd_701_);
v_a_736_ = lean_ctor_get(v_a_725_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v_a_725_, 1);
v_a_714_ = v_a_736_;
goto v___jp_713_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_del_object(v___x_708_);
lean_del_object(v___x_703_);
lean_dec(v_snd_701_);
v_a_738_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_724_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_724_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_del_object(v___x_708_);
lean_dec(v_snd_701_);
v_a_714_ = v___x_711_;
goto v___jp_713_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_del_object(v___x_708_);
lean_dec_ref(v_p_706_);
lean_del_object(v___x_703_);
lean_dec(v_snd_701_);
v_a_759_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_710_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_710_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_____s_771_ = _args[0];
lean_object* v_isLower_772_ = _args[1];
lean_object* v_as_773_ = _args[2];
lean_object* v_sz_774_ = _args[3];
lean_object* v_i_775_ = _args[4];
lean_object* v_b_776_ = _args[5];
lean_object* v___y_777_ = _args[6];
lean_object* v___y_778_ = _args[7];
lean_object* v___y_779_ = _args[8];
lean_object* v___y_780_ = _args[9];
lean_object* v___y_781_ = _args[10];
lean_object* v___y_782_ = _args[11];
lean_object* v___y_783_ = _args[12];
lean_object* v___y_784_ = _args[13];
lean_object* v___y_785_ = _args[14];
lean_object* v___y_786_ = _args[15];
lean_object* v___y_787_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_788_; size_t v_sz_boxed_789_; size_t v_i_boxed_790_; lean_object* v_res_791_; 
v_isLower_boxed_788_ = lean_unbox(v_isLower_772_);
v_sz_boxed_789_ = lean_unbox_usize(v_sz_774_);
lean_dec(v_sz_774_);
v_i_boxed_790_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_res_791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_771_, v_isLower_boxed_788_, v_as_773_, v_sz_boxed_789_, v_i_boxed_790_, v_b_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v_as_773_);
lean_dec(v_____s_771_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(lean_object* v_init_792_, lean_object* v_____s_793_, uint8_t v_isLower_794_, lean_object* v_n_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
if (lean_obj_tag(v_n_795_) == 0)
{
lean_object* v_cs_808_; lean_object* v___x_809_; lean_object* v___x_810_; size_t v_sz_811_; size_t v___x_812_; lean_object* v___x_813_; 
v_cs_808_ = lean_ctor_get(v_n_795_, 0);
v___x_809_ = lean_box(0);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v_b_796_);
v_sz_811_ = lean_array_size(v_cs_808_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_792_, v_____s_793_, v_isLower_794_, v_cs_808_, v_sz_811_, v___x_812_, v___x_810_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_828_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_828_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_fst_818_; 
v_fst_818_ = lean_ctor_get(v_a_814_, 0);
if (lean_obj_tag(v_fst_818_) == 0)
{
lean_object* v_snd_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v_snd_819_ = lean_ctor_get(v_a_814_, 1);
lean_inc(v_snd_819_);
lean_dec(v_a_814_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_snd_819_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_820_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; 
lean_inc_ref(v_fst_818_);
lean_dec(v_a_814_);
v_val_824_ = lean_ctor_get(v_fst_818_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v_fst_818_, 1);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_val_824_);
v___x_826_ = v___x_816_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_813_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_813_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_vs_837_; lean_object* v___x_838_; lean_object* v___x_839_; size_t v_sz_840_; size_t v___x_841_; lean_object* v___x_842_; 
v_vs_837_ = lean_ctor_get(v_n_795_, 0);
v___x_838_ = lean_box(0);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_b_796_);
v_sz_840_ = lean_array_size(v_vs_837_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_793_, v_isLower_794_, v_vs_837_, v_sz_840_, v___x_841_, v___x_839_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_857_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_857_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_fst_847_; 
v_fst_847_ = lean_ctor_get(v_a_843_, 0);
if (lean_obj_tag(v_fst_847_) == 0)
{
lean_object* v_snd_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v_snd_848_ = lean_ctor_get(v_a_843_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_843_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_snd_848_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_849_);
v___x_851_ = v___x_845_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v_val_853_; lean_object* v___x_855_; 
lean_inc_ref(v_fst_847_);
lean_dec(v_a_843_);
v_val_853_ = lean_ctor_get(v_fst_847_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v_fst_847_, 1);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v_val_853_);
v___x_855_ = v___x_845_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_val_853_);
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
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_842_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_842_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_init_866_, lean_object* v_____s_867_, uint8_t v_isLower_868_, lean_object* v_as_869_, size_t v_sz_870_, size_t v_i_871_, lean_object* v_b_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_b_872_);
return v___x_885_;
}
else
{
lean_object* v_snd_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_920_; 
v_snd_886_ = lean_ctor_get(v_b_872_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_b_872_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v_b_872_, 0);
lean_dec(v_unused_921_);
v___x_888_ = v_b_872_;
v_isShared_889_ = v_isSharedCheck_920_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_snd_886_);
lean_dec(v_b_872_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_920_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_a_890_; lean_object* v___x_891_; 
v_a_890_ = lean_array_uget_borrowed(v_as_869_, v_i_871_);
lean_inc(v_snd_886_);
v___x_891_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_866_, v_____s_867_, v_isLower_868_, v_a_890_, v_snd_886_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_911_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_911_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_911_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_911_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
if (lean_obj_tag(v_a_892_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_a_892_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_896_);
v___x_898_ = v___x_888_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_snd_886_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_898_);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
lean_del_object(v___x_894_);
lean_dec(v_snd_886_);
v_a_903_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v_a_892_, 1);
v___x_904_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_a_903_);
lean_ctor_set(v___x_888_, 0, v___x_904_);
v___x_906_ = v___x_888_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_a_903_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
size_t v___x_907_; size_t v___x_908_; 
v___x_907_ = ((size_t)1ULL);
v___x_908_ = lean_usize_add(v_i_871_, v___x_907_);
v_i_871_ = v___x_908_;
v_b_872_ = v___x_906_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_del_object(v___x_888_);
lean_dec(v_snd_886_);
v_a_912_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_891_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_891_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_922_ = _args[0];
lean_object* v_____s_923_ = _args[1];
lean_object* v_isLower_924_ = _args[2];
lean_object* v_as_925_ = _args[3];
lean_object* v_sz_926_ = _args[4];
lean_object* v_i_927_ = _args[5];
lean_object* v_b_928_ = _args[6];
lean_object* v___y_929_ = _args[7];
lean_object* v___y_930_ = _args[8];
lean_object* v___y_931_ = _args[9];
lean_object* v___y_932_ = _args[10];
lean_object* v___y_933_ = _args[11];
lean_object* v___y_934_ = _args[12];
lean_object* v___y_935_ = _args[13];
lean_object* v___y_936_ = _args[14];
lean_object* v___y_937_ = _args[15];
lean_object* v___y_938_ = _args[16];
lean_object* v___y_939_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_940_; size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_isLower_boxed_940_ = lean_unbox(v_isLower_924_);
v_sz_boxed_941_ = lean_unbox_usize(v_sz_926_);
lean_dec(v_sz_926_);
v_i_boxed_942_ = lean_unbox_usize(v_i_927_);
lean_dec(v_i_927_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_922_, v_____s_923_, v_isLower_boxed_940_, v_as_925_, v_sz_boxed_941_, v_i_boxed_942_, v_b_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v_as_925_);
lean_dec(v_____s_923_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1___boxed(lean_object* v_init_944_, lean_object* v_____s_945_, lean_object* v_isLower_946_, lean_object* v_n_947_, lean_object* v_b_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v_isLower_boxed_960_; lean_object* v_res_961_; 
v_isLower_boxed_960_ = lean_unbox(v_isLower_946_);
v_res_961_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_944_, v_____s_945_, v_isLower_boxed_960_, v_n_947_, v_b_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v_n_947_);
lean_dec(v_____s_945_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(lean_object* v_____s_962_, uint8_t v_isLower_963_, lean_object* v_t_964_, lean_object* v_init_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_root_977_; lean_object* v_tail_978_; lean_object* v___x_979_; 
v_root_977_ = lean_ctor_get(v_t_964_, 0);
v_tail_978_ = lean_ctor_get(v_t_964_, 1);
v___x_979_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_965_, v_____s_962_, v_isLower_963_, v_root_977_, v_init_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1016_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_1016_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1016_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
if (lean_obj_tag(v_a_980_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; 
v_a_984_ = lean_ctor_get(v_a_980_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v_a_980_, 1);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v_a_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; size_t v_sz_991_; size_t v___x_992_; lean_object* v___x_993_; 
lean_del_object(v___x_982_);
v_a_988_ = lean_ctor_get(v_a_980_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v_a_980_, 1);
v___x_989_ = lean_box(0);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v_a_988_);
v_sz_991_ = lean_array_size(v_tail_978_);
v___x_992_ = ((size_t)0ULL);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_962_, v_isLower_963_, v_tail_978_, v_sz_991_, v___x_992_, v___x_990_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1007_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_fst_998_; 
v_fst_998_ = lean_ctor_get(v_a_994_, 0);
if (lean_obj_tag(v_fst_998_) == 0)
{
lean_object* v_snd_999_; lean_object* v___x_1001_; 
v_snd_999_ = lean_ctor_get(v_a_994_, 1);
lean_inc(v_snd_999_);
lean_dec(v_a_994_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_snd_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_snd_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v_val_1003_; lean_object* v___x_1005_; 
lean_inc_ref(v_fst_998_);
lean_dec(v_a_994_);
v_val_1003_ = lean_ctor_get(v_fst_998_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v_fst_998_, 1);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_val_1003_);
v___x_1005_ = v___x_996_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_val_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_993_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_993_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_979_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_979_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1025_, lean_object* v_isLower_1026_, lean_object* v_t_1027_, lean_object* v_init_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_isLower_boxed_1040_; lean_object* v_res_1041_; 
v_isLower_boxed_1040_ = lean_unbox(v_isLower_1026_);
v_res_1041_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_____s_1025_, v_isLower_boxed_1040_, v_t_1027_, v_init_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v_t_1027_);
lean_dec(v_____s_1025_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1042_, lean_object* v_as_1043_, size_t v_sz_1044_, size_t v_i_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_usize_dec_lt(v_i_1045_, v_sz_1044_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_b_1046_);
return v___x_1059_;
}
else
{
lean_object* v_snd_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1084_; 
v_snd_1060_ = lean_ctor_get(v_b_1046_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_b_1046_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_b_1046_, 0);
lean_dec(v_unused_1085_);
v___x_1062_ = v_b_1046_;
v_isShared_1063_ = v_isSharedCheck_1084_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_snd_1060_);
lean_dec(v_b_1046_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1084_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1064_ = lean_array_uget_borrowed(v_as_1043_, v_i_1045_);
v___x_1065_ = lean_box(0);
v___x_1066_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1060_, v_isLower_1042_, v_a_1064_, v___x_1065_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
lean_dec_ref_known(v___x_1066_, 1);
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_add(v_snd_1060_, v___x_1068_);
lean_dec(v_snd_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1069_);
lean_ctor_set(v___x_1062_, 0, v___x_1067_);
v___x_1071_ = v___x_1062_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
size_t v___x_1072_; size_t v___x_1073_; 
v___x_1072_ = ((size_t)1ULL);
v___x_1073_ = lean_usize_add(v_i_1045_, v___x_1072_);
v_i_1045_ = v___x_1073_;
v_b_1046_ = v___x_1071_;
goto _start;
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_del_object(v___x_1062_);
lean_dec(v_snd_1060_);
v_a_1076_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1066_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1066_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object* v_isLower_1086_, lean_object* v_as_1087_, lean_object* v_sz_1088_, lean_object* v_i_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v_isLower_boxed_1102_; size_t v_sz_boxed_1103_; size_t v_i_boxed_1104_; lean_object* v_res_1105_; 
v_isLower_boxed_1102_ = lean_unbox(v_isLower_1086_);
v_sz_boxed_1103_ = lean_unbox_usize(v_sz_1088_);
lean_dec(v_sz_1088_);
v_i_boxed_1104_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_res_1105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_1102_, v_as_1087_, v_sz_boxed_1103_, v_i_boxed_1104_, v_b_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v_as_1087_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1106_, lean_object* v_as_1107_, size_t v_sz_1108_, size_t v_i_1109_, lean_object* v_b_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_usize_dec_lt(v_i_1109_, v_sz_1108_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_b_1110_);
return v___x_1123_;
}
else
{
lean_object* v_snd_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1148_; 
v_snd_1124_ = lean_ctor_get(v_b_1110_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_b_1110_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_b_1110_, 0);
lean_dec(v_unused_1149_);
v___x_1126_ = v_b_1110_;
v_isShared_1127_ = v_isSharedCheck_1148_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_snd_1124_);
lean_dec(v_b_1110_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1148_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_a_1128_ = lean_array_uget_borrowed(v_as_1107_, v_i_1109_);
v___x_1129_ = lean_box(0);
v___x_1130_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1124_, v_isLower_1106_, v_a_1128_, v___x_1129_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_dec_ref_known(v___x_1130_, 1);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_add(v_snd_1124_, v___x_1132_);
lean_dec(v_snd_1124_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v___x_1133_);
lean_ctor_set(v___x_1126_, 0, v___x_1131_);
v___x_1135_ = v___x_1126_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_add(v_i_1109_, v___x_1136_);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1106_, v_as_1107_, v_sz_1108_, v___x_1137_, v___x_1135_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
return v___x_1138_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_1126_);
lean_dec(v_snd_1124_);
v_a_1140_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1130_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1130_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5___boxed(lean_object* v_isLower_1150_, lean_object* v_as_1151_, lean_object* v_sz_1152_, lean_object* v_i_1153_, lean_object* v_b_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_isLower_boxed_1166_; size_t v_sz_boxed_1167_; size_t v_i_boxed_1168_; lean_object* v_res_1169_; 
v_isLower_boxed_1166_ = lean_unbox(v_isLower_1150_);
v_sz_boxed_1167_ = lean_unbox_usize(v_sz_1152_);
lean_dec(v_sz_1152_);
v_i_boxed_1168_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1166_, v_as_1151_, v_sz_boxed_1167_, v_i_boxed_1168_, v_b_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v_as_1151_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1170_, lean_object* v_as_1171_, size_t v_sz_1172_, size_t v_i_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_lt(v_i_1173_, v_sz_1172_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_b_1174_);
return v___x_1187_;
}
else
{
lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1212_; 
v_snd_1188_ = lean_ctor_get(v_b_1174_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_b_1174_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_b_1174_, 0);
lean_dec(v_unused_1213_);
v___x_1190_ = v_b_1174_;
v_isShared_1191_ = v_isSharedCheck_1212_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_dec(v_b_1174_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1212_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_a_1192_ = lean_array_uget_borrowed(v_as_1171_, v_i_1173_);
v___x_1193_ = lean_box(0);
v___x_1194_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1188_, v_isLower_1170_, v_a_1192_, v___x_1193_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_dec_ref_known(v___x_1194_, 1);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = lean_nat_add(v_snd_1188_, v___x_1196_);
lean_dec(v_snd_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1197_);
lean_ctor_set(v___x_1190_, 0, v___x_1195_);
v___x_1199_ = v___x_1190_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
size_t v___x_1200_; size_t v___x_1201_; 
v___x_1200_ = ((size_t)1ULL);
v___x_1201_ = lean_usize_add(v_i_1173_, v___x_1200_);
v_i_1173_ = v___x_1201_;
v_b_1174_ = v___x_1199_;
goto _start;
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_del_object(v___x_1190_);
lean_dec(v_snd_1188_);
v_a_1204_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1194_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1194_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object* v_isLower_1214_, lean_object* v_as_1215_, lean_object* v_sz_1216_, lean_object* v_i_1217_, lean_object* v_b_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v_isLower_boxed_1230_; size_t v_sz_boxed_1231_; size_t v_i_boxed_1232_; lean_object* v_res_1233_; 
v_isLower_boxed_1230_ = lean_unbox(v_isLower_1214_);
v_sz_boxed_1231_ = lean_unbox_usize(v_sz_1216_);
lean_dec(v_sz_1216_);
v_i_boxed_1232_ = lean_unbox_usize(v_i_1217_);
lean_dec(v_i_1217_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1230_, v_as_1215_, v_sz_boxed_1231_, v_i_boxed_1232_, v_b_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v_as_1215_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1234_, lean_object* v_as_1235_, size_t v_sz_1236_, size_t v_i_1237_, lean_object* v_b_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v___x_1250_; 
v___x_1250_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v_b_1238_);
return v___x_1251_;
}
else
{
lean_object* v_snd_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1276_; 
v_snd_1252_ = lean_ctor_get(v_b_1238_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_b_1238_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; 
v_unused_1277_ = lean_ctor_get(v_b_1238_, 0);
lean_dec(v_unused_1277_);
v___x_1254_ = v_b_1238_;
v_isShared_1255_ = v_isSharedCheck_1276_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_snd_1252_);
lean_dec(v_b_1238_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1276_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_a_1256_ = lean_array_uget_borrowed(v_as_1235_, v_i_1237_);
v___x_1257_ = lean_box(0);
v___x_1258_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1252_, v_isLower_1234_, v_a_1256_, v___x_1257_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
lean_dec_ref_known(v___x_1258_, 1);
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_add(v_snd_1252_, v___x_1260_);
lean_dec(v_snd_1252_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v___x_1261_);
lean_ctor_set(v___x_1254_, 0, v___x_1259_);
v___x_1263_ = v___x_1254_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1237_, v___x_1264_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1234_, v_as_1235_, v_sz_1236_, v___x_1265_, v___x_1263_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
return v___x_1266_;
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_del_object(v___x_1254_);
lean_dec(v_snd_1252_);
v_a_1268_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1258_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1258_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object* v_isLower_1278_, lean_object* v_as_1279_, lean_object* v_sz_1280_, lean_object* v_i_1281_, lean_object* v_b_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v_isLower_boxed_1294_; size_t v_sz_boxed_1295_; size_t v_i_boxed_1296_; lean_object* v_res_1297_; 
v_isLower_boxed_1294_ = lean_unbox(v_isLower_1278_);
v_sz_boxed_1295_ = lean_unbox_usize(v_sz_1280_);
lean_dec(v_sz_1280_);
v_i_boxed_1296_ = lean_unbox_usize(v_i_1281_);
lean_dec(v_i_1281_);
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1294_, v_as_1279_, v_sz_boxed_1295_, v_i_boxed_1296_, v_b_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v_as_1279_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(lean_object* v_init_1298_, uint8_t v_isLower_1299_, lean_object* v_n_1300_, lean_object* v_b_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
if (lean_obj_tag(v_n_1300_) == 0)
{
lean_object* v_cs_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; size_t v_sz_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v_cs_1313_ = lean_ctor_get(v_n_1300_, 0);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v_b_1301_);
v_sz_1316_ = lean_array_size(v_cs_1313_);
v___x_1317_ = ((size_t)0ULL);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1298_, v_isLower_1299_, v_cs_1313_, v_sz_1316_, v___x_1317_, v___x_1315_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1333_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_fst_1323_; 
v_fst_1323_ = lean_ctor_get(v_a_1319_, 0);
if (lean_obj_tag(v_fst_1323_) == 0)
{
lean_object* v_snd_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v_snd_1324_ = lean_ctor_get(v_a_1319_, 1);
lean_inc(v_snd_1324_);
lean_dec(v_a_1319_);
v___x_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_snd_1324_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1325_);
v___x_1327_ = v___x_1321_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
else
{
lean_object* v_val_1329_; lean_object* v___x_1331_; 
lean_inc_ref(v_fst_1323_);
lean_dec(v_a_1319_);
v_val_1329_ = lean_ctor_get(v_fst_1323_, 0);
lean_inc(v_val_1329_);
lean_dec_ref_known(v_fst_1323_, 1);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v_val_1329_);
v___x_1331_ = v___x_1321_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_val_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_a_1334_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1318_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1318_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_vs_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; size_t v_sz_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v_vs_1342_ = lean_ctor_get(v_n_1300_, 0);
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v_b_1301_);
v_sz_1345_ = lean_array_size(v_vs_1342_);
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1299_, v_vs_1342_, v_sz_1345_, v___x_1346_, v___x_1344_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1362_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1362_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1362_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_fst_1352_; 
v_fst_1352_ = lean_ctor_get(v_a_1348_, 0);
if (lean_obj_tag(v_fst_1352_) == 0)
{
lean_object* v_snd_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v_snd_1353_ = lean_ctor_get(v_a_1348_, 1);
lean_inc(v_snd_1353_);
lean_dec(v_a_1348_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_snd_1353_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1354_);
v___x_1356_ = v___x_1350_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
else
{
lean_object* v_val_1358_; lean_object* v___x_1360_; 
lean_inc_ref(v_fst_1352_);
lean_dec(v_a_1348_);
v_val_1358_ = lean_ctor_get(v_fst_1352_, 0);
lean_inc(v_val_1358_);
lean_dec_ref_known(v_fst_1352_, 1);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v_val_1358_);
v___x_1360_ = v___x_1350_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_val_1358_);
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
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_a_1363_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1347_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1347_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object* v_init_1371_, uint8_t v_isLower_1372_, lean_object* v_as_1373_, size_t v_sz_1374_, size_t v_i_1375_, lean_object* v_b_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_lt(v_i_1375_, v_sz_1374_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_b_1376_);
return v___x_1389_;
}
else
{
lean_object* v_snd_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1424_; 
v_snd_1390_ = lean_ctor_get(v_b_1376_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_b_1376_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v_b_1376_, 0);
lean_dec(v_unused_1425_);
v___x_1392_ = v_b_1376_;
v_isShared_1393_ = v_isSharedCheck_1424_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1390_);
lean_dec(v_b_1376_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1424_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_array_uget_borrowed(v_as_1373_, v_i_1375_);
lean_inc(v_snd_1390_);
v___x_1395_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1371_, v_isLower_1372_, v_a_1394_, v_snd_1390_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1415_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1415_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1415_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
if (lean_obj_tag(v_a_1396_) == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_a_1396_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1400_);
v___x_1402_ = v___x_1392_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_snd_1390_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1402_);
v___x_1404_ = v___x_1398_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_del_object(v___x_1398_);
lean_dec(v_snd_1390_);
v_a_1407_ = lean_ctor_get(v_a_1396_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v_a_1396_, 1);
v___x_1408_ = lean_box(0);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v_a_1407_);
lean_ctor_set(v___x_1392_, 0, v___x_1408_);
v___x_1410_ = v___x_1392_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_a_1407_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
size_t v___x_1411_; size_t v___x_1412_; 
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_add(v_i_1375_, v___x_1411_);
v_i_1375_ = v___x_1412_;
v_b_1376_ = v___x_1410_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_del_object(v___x_1392_);
lean_dec(v_snd_1390_);
v_a_1416_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1395_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1395_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_init_1426_ = _args[0];
lean_object* v_isLower_1427_ = _args[1];
lean_object* v_as_1428_ = _args[2];
lean_object* v_sz_1429_ = _args[3];
lean_object* v_i_1430_ = _args[4];
lean_object* v_b_1431_ = _args[5];
lean_object* v___y_1432_ = _args[6];
lean_object* v___y_1433_ = _args[7];
lean_object* v___y_1434_ = _args[8];
lean_object* v___y_1435_ = _args[9];
lean_object* v___y_1436_ = _args[10];
lean_object* v___y_1437_ = _args[11];
lean_object* v___y_1438_ = _args[12];
lean_object* v___y_1439_ = _args[13];
lean_object* v___y_1440_ = _args[14];
lean_object* v___y_1441_ = _args[15];
lean_object* v___y_1442_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1443_; size_t v_sz_boxed_1444_; size_t v_i_boxed_1445_; lean_object* v_res_1446_; 
v_isLower_boxed_1443_ = lean_unbox(v_isLower_1427_);
v_sz_boxed_1444_ = lean_unbox_usize(v_sz_1429_);
lean_dec(v_sz_1429_);
v_i_boxed_1445_ = lean_unbox_usize(v_i_1430_);
lean_dec(v_i_1430_);
v_res_1446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1426_, v_isLower_boxed_1443_, v_as_1428_, v_sz_boxed_1444_, v_i_boxed_1445_, v_b_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v_as_1428_);
lean_dec(v_init_1426_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_init_1447_, lean_object* v_isLower_1448_, lean_object* v_n_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
uint8_t v_isLower_boxed_1462_; lean_object* v_res_1463_; 
v_isLower_boxed_1462_ = lean_unbox(v_isLower_1448_);
v_res_1463_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1447_, v_isLower_boxed_1462_, v_n_1449_, v_b_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v_n_1449_);
lean_dec(v_init_1447_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(uint8_t v_isLower_1464_, lean_object* v_t_1465_, lean_object* v_init_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_root_1478_; lean_object* v_tail_1479_; lean_object* v___x_1480_; 
v_root_1478_ = lean_ctor_get(v_t_1465_, 0);
v_tail_1479_ = lean_ctor_get(v_t_1465_, 1);
lean_inc(v_init_1466_);
v___x_1480_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1466_, v_isLower_1464_, v_root_1478_, v_init_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v_init_1466_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1517_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1517_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1517_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
if (lean_obj_tag(v_a_1481_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; 
v_a_1485_ = lean_ctor_get(v_a_1481_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v_a_1481_, 1);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v_a_1485_);
v___x_1487_ = v___x_1483_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; size_t v_sz_1492_; size_t v___x_1493_; lean_object* v___x_1494_; 
lean_del_object(v___x_1483_);
v_a_1489_ = lean_ctor_get(v_a_1481_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v_a_1481_, 1);
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v_a_1489_);
v_sz_1492_ = lean_array_size(v_tail_1479_);
v___x_1493_ = ((size_t)0ULL);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_1464_, v_tail_1479_, v_sz_1492_, v___x_1493_, v___x_1491_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1508_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1508_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1508_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_fst_1499_; 
v_fst_1499_ = lean_ctor_get(v_a_1495_, 0);
if (lean_obj_tag(v_fst_1499_) == 0)
{
lean_object* v_snd_1500_; lean_object* v___x_1502_; 
v_snd_1500_ = lean_ctor_get(v_a_1495_, 1);
lean_inc(v_snd_1500_);
lean_dec(v_a_1495_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_snd_1500_);
v___x_1502_ = v___x_1497_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_snd_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
else
{
lean_object* v_val_1504_; lean_object* v___x_1506_; 
lean_inc_ref(v_fst_1499_);
lean_dec(v_a_1495_);
v_val_1504_ = lean_ctor_get(v_fst_1499_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v_fst_1499_, 1);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_val_1504_);
v___x_1506_ = v___x_1497_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_val_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1509_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1494_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1494_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_a_1518_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1480_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1480_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1526_, lean_object* v_t_1527_, lean_object* v_init_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
uint8_t v_isLower_boxed_1540_; lean_object* v_res_1541_; 
v_isLower_boxed_1540_ = lean_unbox(v_isLower_1526_);
v_res_1541_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_boxed_1540_, v_t_1527_, v_init_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v_t_1527_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(lean_object* v_css_1542_, uint8_t v_isLower_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_x_1555_; lean_object* v___x_1556_; 
v_x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_1543_, v_css_1542_, v_x_1555_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1564_; 
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v___x_1556_, 0);
lean_dec(v_unused_1565_);
v___x_1558_ = v___x_1556_;
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
else
{
lean_dec(v___x_1556_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1560_ = lean_box(0);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1560_);
v___x_1562_ = v___x_1558_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_a_1566_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1556_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1556_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs___boxed(lean_object* v_css_1574_, lean_object* v_isLower_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
uint8_t v_isLower_boxed_1587_; lean_object* v_res_1588_; 
v_isLower_boxed_1587_ = lean_unbox(v_isLower_1575_);
v_res_1588_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_css_1574_, v_isLower_boxed_1587_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_css_1574_);
return v_res_1588_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1591_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1));
v___x_1592_ = lean_unsigned_to_nat(2u);
v___x_1593_ = lean_unsigned_to_nat(55u);
v___x_1594_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0));
v___x_1595_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1596_ = l_mkPanicMessageWithDecl(v___x_1595_, v___x_1594_, v___x_1593_, v___x_1592_, v___x_1591_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1597_, v_a_1605_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v_lowers_1610_; lean_object* v_vars_1611_; lean_object* v_size_1612_; lean_object* v_size_1613_; uint8_t v___x_1614_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v_lowers_1610_ = lean_ctor_get(v_a_1609_, 7);
lean_inc_ref(v_lowers_1610_);
v_vars_1611_ = lean_ctor_get(v_a_1609_, 0);
lean_inc_ref(v_vars_1611_);
lean_dec(v_a_1609_);
v_size_1612_ = lean_ctor_get(v_lowers_1610_, 2);
v_size_1613_ = lean_ctor_get(v_vars_1611_, 2);
lean_inc(v_size_1613_);
lean_dec_ref(v_vars_1611_);
v___x_1614_ = lean_nat_dec_eq(v_size_1612_, v_size_1613_);
lean_dec(v_size_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec_ref(v_lowers_1610_);
v___x_1615_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2);
v___x_1616_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_1615_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_lowers_1610_, v___x_1614_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec_ref(v_lowers_1610_);
return v___x_1617_;
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_a_1618_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1608_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1608_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___boxed(lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec(v_a_1626_);
return v_res_1637_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1640_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1));
v___x_1641_ = lean_unsigned_to_nat(2u);
v___x_1642_ = lean_unsigned_to_nat(60u);
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0));
v___x_1644_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1645_ = l_mkPanicMessageWithDecl(v___x_1644_, v___x_1643_, v___x_1642_, v___x_1641_, v___x_1640_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1646_, v_a_1654_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v_uppers_1659_; lean_object* v_vars_1660_; lean_object* v_size_1661_; lean_object* v_size_1662_; uint8_t v___x_1663_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v_uppers_1659_ = lean_ctor_get(v_a_1658_, 8);
lean_inc_ref(v_uppers_1659_);
v_vars_1660_ = lean_ctor_get(v_a_1658_, 0);
lean_inc_ref(v_vars_1660_);
lean_dec(v_a_1658_);
v_size_1661_ = lean_ctor_get(v_uppers_1659_, 2);
v_size_1662_ = lean_ctor_get(v_vars_1660_, 2);
lean_inc(v_size_1662_);
lean_dec_ref(v_vars_1660_);
v___x_1663_ = lean_nat_dec_eq(v_size_1661_, v_size_1662_);
lean_dec(v_size_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec_ref(v_uppers_1659_);
v___x_1664_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2);
v___x_1665_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_1664_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
return v___x_1665_;
}
else
{
uint8_t v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = 0;
v___x_1667_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_uppers_1659_, v___x_1666_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec_ref(v_uppers_1659_);
return v___x_1667_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1657_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1657_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___boxed(lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec(v_a_1676_);
return v_res_1687_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(lean_object* v_msg_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_4077__overap_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0);
v___x_4077__overap_1702_ = lean_panic_fn_borrowed(v___x_1701_, v_msg_1689_);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1691_);
lean_inc(v___y_1690_);
v___x_1703_ = lean_apply_11(v___x_4077__overap_1702_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, lean_box(0));
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___boxed(lean_object* v_msg_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v_msg_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec(v___y_1705_);
return v_res_1716_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = lean_nat_to_int(v___x_1717_);
return v___x_1718_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2));
v___x_1722_ = lean_unsigned_to_nat(6u);
v___x_1723_ = lean_unsigned_to_nat(70u);
v___x_1724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_1725_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1726_ = l_mkPanicMessageWithDecl(v___x_1725_, v___x_1724_, v___x_1723_, v___x_1722_, v___x_1721_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1727_, size_t v_sz_1728_, size_t v_i_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_usize_dec_lt(v_i_1729_, v_sz_1728_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_b_1730_);
return v___x_1743_;
}
else
{
lean_object* v_snd_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1802_; 
v_snd_1744_ = lean_ctor_get(v_b_1730_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_b_1730_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_b_1730_, 0);
lean_dec(v_unused_1803_);
v___x_1746_ = v_b_1730_;
v_isShared_1747_ = v_isSharedCheck_1802_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_snd_1744_);
lean_dec(v_b_1730_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1802_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v_a_1750_; lean_object* v_a_1760_; 
v___x_1748_ = lean_box(0);
v_a_1760_ = lean_array_uget(v_as_1727_, v_i_1729_);
if (lean_obj_tag(v_a_1760_) == 1)
{
lean_object* v_val_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1801_; 
v_val_1761_ = lean_ctor_get(v_a_1760_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_a_1760_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1763_ = v_a_1760_;
v_isShared_1764_ = v_isSharedCheck_1801_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_val_1761_);
lean_dec(v_a_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1801_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_d_1765_; lean_object* v_p_1766_; lean_object* v___x_1767_; 
v_d_1765_ = lean_ctor_get(v_val_1761_, 0);
lean_inc(v_d_1765_);
v_p_1766_ = lean_ctor_get(v_val_1761_, 1);
lean_inc_ref(v_p_1766_);
lean_dec(v_val_1761_);
v___x_1767_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_1766_, v_snd_1744_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec_ref(v_p_1766_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
lean_dec_ref_known(v___x_1767_, 1);
v___x_1768_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1769_ = lean_int_dec_lt(v___x_1768_, v_d_1765_);
lean_dec(v_d_1765_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1771_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1770_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1784_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1784_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1784_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_object* v___x_1777_; 
lean_del_object(v___x_1746_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v_a_1772_);
v___x_1777_ = v___x_1763_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
lean_ctor_set(v___x_1778_, 1, v_snd_1744_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1778_);
v___x_1780_ = v___x_1774_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
else
{
lean_object* v_a_1783_; 
lean_del_object(v___x_1774_);
lean_del_object(v___x_1763_);
lean_dec(v_snd_1744_);
v_a_1783_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v_a_1772_, 1);
v_a_1750_ = v_a_1783_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_del_object(v___x_1763_);
lean_del_object(v___x_1746_);
lean_dec(v_snd_1744_);
v_a_1785_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1771_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1771_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_del_object(v___x_1763_);
goto v___jp_1757_;
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_d_1765_);
lean_del_object(v___x_1763_);
lean_del_object(v___x_1746_);
lean_dec(v_snd_1744_);
v_a_1793_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1767_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1767_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
else
{
lean_dec(v_a_1760_);
goto v___jp_1757_;
}
v___jp_1749_:
{
lean_object* v___x_1752_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v_a_1750_);
lean_ctor_set(v___x_1746_, 0, v___x_1748_);
v___x_1752_ = v___x_1746_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_a_1750_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
size_t v___x_1753_; size_t v___x_1754_; 
v___x_1753_ = ((size_t)1ULL);
v___x_1754_ = lean_usize_add(v_i_1729_, v___x_1753_);
v_i_1729_ = v___x_1754_;
v_b_1730_ = v___x_1752_;
goto _start;
}
}
v___jp_1757_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_nat_add(v_snd_1744_, v___x_1758_);
lean_dec(v_snd_1744_);
v_a_1750_ = v___x_1759_;
goto v___jp_1749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1804_, lean_object* v_sz_1805_, lean_object* v_i_1806_, lean_object* v_b_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
size_t v_sz_boxed_1819_; size_t v_i_boxed_1820_; lean_object* v_res_1821_; 
v_sz_boxed_1819_ = lean_unbox_usize(v_sz_1805_);
lean_dec(v_sz_1805_);
v_i_boxed_1820_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1804_, v_sz_boxed_1819_, v_i_boxed_1820_, v_b_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v_as_1804_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(lean_object* v_as_1822_, size_t v_sz_1823_, size_t v_i_1824_, lean_object* v_b_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_usize_dec_lt(v_i_1824_, v_sz_1823_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_b_1825_);
return v___x_1838_;
}
else
{
lean_object* v_snd_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1897_; 
v_snd_1839_ = lean_ctor_get(v_b_1825_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_b_1825_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_b_1825_, 0);
lean_dec(v_unused_1898_);
v___x_1841_ = v_b_1825_;
v_isShared_1842_ = v_isSharedCheck_1897_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_snd_1839_);
lean_dec(v_b_1825_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1897_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v_a_1845_; lean_object* v_a_1855_; 
v___x_1843_ = lean_box(0);
v_a_1855_ = lean_array_uget(v_as_1822_, v_i_1824_);
if (lean_obj_tag(v_a_1855_) == 1)
{
lean_object* v_val_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1896_; 
v_val_1856_ = lean_ctor_get(v_a_1855_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_a_1855_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1858_ = v_a_1855_;
v_isShared_1859_ = v_isSharedCheck_1896_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_val_1856_);
lean_dec(v_a_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1896_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_d_1860_; lean_object* v_p_1861_; lean_object* v___x_1862_; 
v_d_1860_ = lean_ctor_get(v_val_1856_, 0);
lean_inc(v_d_1860_);
v_p_1861_ = lean_ctor_get(v_val_1856_, 1);
lean_inc_ref(v_p_1861_);
lean_dec(v_val_1856_);
v___x_1862_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_1861_, v_snd_1839_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec_ref(v_p_1861_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
lean_dec_ref_known(v___x_1862_, 1);
v___x_1863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1864_ = lean_int_dec_lt(v___x_1863_, v_d_1860_);
lean_dec(v_d_1860_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1866_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1865_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1879_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1879_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1879_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
if (lean_obj_tag(v_a_1867_) == 0)
{
lean_object* v___x_1872_; 
lean_del_object(v___x_1841_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v_a_1867_);
v___x_1872_ = v___x_1858_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v_snd_1839_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1873_);
v___x_1875_ = v___x_1869_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_object* v_a_1878_; 
lean_del_object(v___x_1869_);
lean_del_object(v___x_1858_);
lean_dec(v_snd_1839_);
v_a_1878_ = lean_ctor_get(v_a_1867_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v_a_1867_, 1);
v_a_1845_ = v_a_1878_;
goto v___jp_1844_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_del_object(v___x_1858_);
lean_del_object(v___x_1841_);
lean_dec(v_snd_1839_);
v_a_1880_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1866_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1866_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_del_object(v___x_1858_);
goto v___jp_1852_;
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_d_1860_);
lean_del_object(v___x_1858_);
lean_del_object(v___x_1841_);
lean_dec(v_snd_1839_);
v_a_1888_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1862_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1862_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
else
{
lean_dec(v_a_1855_);
goto v___jp_1852_;
}
v___jp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v_a_1845_);
lean_ctor_set(v___x_1841_, 0, v___x_1843_);
v___x_1847_ = v___x_1841_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_a_1845_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = ((size_t)1ULL);
v___x_1849_ = lean_usize_add(v_i_1824_, v___x_1848_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1822_, v_sz_1823_, v___x_1849_, v___x_1847_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
return v___x_1850_;
}
}
v___jp_1852_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_add(v_snd_1839_, v___x_1853_);
lean_dec(v_snd_1839_);
v_a_1845_ = v___x_1854_;
goto v___jp_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1899_, lean_object* v_sz_1900_, lean_object* v_i_1901_, lean_object* v_b_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
size_t v_sz_boxed_1914_; size_t v_i_boxed_1915_; lean_object* v_res_1916_; 
v_sz_boxed_1914_ = lean_unbox_usize(v_sz_1900_);
lean_dec(v_sz_1900_);
v_i_boxed_1915_ = lean_unbox_usize(v_i_1901_);
lean_dec(v_i_1901_);
v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_as_1899_, v_sz_boxed_1914_, v_i_boxed_1915_, v_b_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v_as_1899_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(lean_object* v_init_1917_, lean_object* v_n_1918_, lean_object* v_b_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
if (lean_obj_tag(v_n_1918_) == 0)
{
lean_object* v_cs_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v_cs_1931_ = lean_ctor_get(v_n_1918_, 0);
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v_b_1919_);
v_sz_1934_ = lean_array_size(v_cs_1931_);
v___x_1935_ = ((size_t)0ULL);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_1917_, v_cs_1931_, v_sz_1934_, v___x_1935_, v___x_1933_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1951_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1951_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1951_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_fst_1941_; 
v_fst_1941_ = lean_ctor_get(v_a_1937_, 0);
if (lean_obj_tag(v_fst_1941_) == 0)
{
lean_object* v_snd_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v_snd_1942_ = lean_ctor_get(v_a_1937_, 1);
lean_inc(v_snd_1942_);
lean_dec(v_a_1937_);
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_snd_1942_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1943_);
v___x_1945_ = v___x_1939_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
else
{
lean_object* v_val_1947_; lean_object* v___x_1949_; 
lean_inc_ref(v_fst_1941_);
lean_dec(v_a_1937_);
v_val_1947_ = lean_ctor_get(v_fst_1941_, 0);
lean_inc(v_val_1947_);
lean_dec_ref_known(v_fst_1941_, 1);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v_val_1947_);
v___x_1949_ = v___x_1939_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_val_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_a_1952_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1936_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1936_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_vs_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; size_t v_sz_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v_vs_1960_ = lean_ctor_get(v_n_1918_, 0);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v_b_1919_);
v_sz_1963_ = lean_array_size(v_vs_1960_);
v___x_1964_ = ((size_t)0ULL);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_vs_1960_, v_sz_1963_, v___x_1964_, v___x_1962_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1980_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1980_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1980_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_fst_1970_; 
v_fst_1970_ = lean_ctor_get(v_a_1966_, 0);
if (lean_obj_tag(v_fst_1970_) == 0)
{
lean_object* v_snd_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v_snd_1971_ = lean_ctor_get(v_a_1966_, 1);
lean_inc(v_snd_1971_);
lean_dec(v_a_1966_);
v___x_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_snd_1971_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1972_);
v___x_1974_ = v___x_1968_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
else
{
lean_object* v_val_1976_; lean_object* v___x_1978_; 
lean_inc_ref(v_fst_1970_);
lean_dec(v_a_1966_);
v_val_1976_ = lean_ctor_get(v_fst_1970_, 0);
lean_inc(v_val_1976_);
lean_dec_ref_known(v_fst_1970_, 1);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v_val_1976_);
v___x_1978_ = v___x_1968_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_val_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1965_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1965_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(lean_object* v_init_1989_, lean_object* v_as_1990_, size_t v_sz_1991_, size_t v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_1993_);
return v___x_2006_;
}
else
{
lean_object* v_snd_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2041_; 
v_snd_2007_ = lean_ctor_get(v_b_1993_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_b_1993_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_b_1993_, 0);
lean_dec(v_unused_2042_);
v___x_2009_ = v_b_1993_;
v_isShared_2010_ = v_isSharedCheck_2041_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2007_);
lean_dec(v_b_1993_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2041_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_array_uget_borrowed(v_as_1990_, v_i_1992_);
lean_inc(v_snd_2007_);
v___x_2012_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_1989_, v_a_2011_, v_snd_2007_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2032_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2032_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2032_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
if (lean_obj_tag(v_a_2013_) == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_a_2013_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2017_);
v___x_2019_ = v___x_2009_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_snd_2007_);
v___x_2019_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2019_);
v___x_2021_ = v___x_2015_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_del_object(v___x_2015_);
lean_dec(v_snd_2007_);
v_a_2024_ = lean_ctor_get(v_a_2013_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v_a_2013_, 1);
v___x_2025_ = lean_box(0);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v_a_2024_);
lean_ctor_set(v___x_2009_, 0, v___x_2025_);
v___x_2027_ = v___x_2009_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_a_2024_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
size_t v___x_2028_; size_t v___x_2029_; 
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_add(v_i_1992_, v___x_2028_);
v_i_1992_ = v___x_2029_;
v_b_1993_ = v___x_2027_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_del_object(v___x_2009_);
lean_dec(v_snd_2007_);
v_a_2033_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2012_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2012_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2___boxed(lean_object* v_init_2043_, lean_object* v_as_2044_, lean_object* v_sz_2045_, lean_object* v_i_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
size_t v_sz_boxed_2059_; size_t v_i_boxed_2060_; lean_object* v_res_2061_; 
v_sz_boxed_2059_ = lean_unbox_usize(v_sz_2045_);
lean_dec(v_sz_2045_);
v_i_boxed_2060_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_2043_, v_as_2044_, v_sz_boxed_2059_, v_i_boxed_2060_, v_b_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v_as_2044_);
lean_dec(v_init_2043_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1___boxed(lean_object* v_init_2062_, lean_object* v_n_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2062_, v_n_2063_, v_b_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
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
lean_dec_ref(v_n_2063_);
lean_dec(v_init_2062_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(lean_object* v_as_2077_, size_t v_sz_2078_, size_t v_i_2079_, lean_object* v_b_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_usize_dec_lt(v_i_2079_, v_sz_2078_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_b_2080_);
return v___x_2093_;
}
else
{
lean_object* v_snd_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2153_; 
v_snd_2094_ = lean_ctor_get(v_b_2080_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_b_2080_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; 
v_unused_2154_ = lean_ctor_get(v_b_2080_, 0);
lean_dec(v_unused_2154_);
v___x_2096_ = v_b_2080_;
v_isShared_2097_ = v_isSharedCheck_2153_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_snd_2094_);
lean_dec(v_b_2080_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2153_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v_a_2100_; lean_object* v_a_2110_; 
v___x_2098_ = lean_box(0);
v_a_2110_ = lean_array_uget(v_as_2077_, v_i_2079_);
if (lean_obj_tag(v_a_2110_) == 1)
{
lean_object* v_val_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2152_; 
v_val_2111_ = lean_ctor_get(v_a_2110_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_a_2110_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2113_ = v_a_2110_;
v_isShared_2114_ = v_isSharedCheck_2152_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_val_2111_);
lean_dec(v_a_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2152_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_d_2115_; lean_object* v_p_2116_; lean_object* v___x_2117_; 
v_d_2115_ = lean_ctor_get(v_val_2111_, 0);
lean_inc(v_d_2115_);
v_p_2116_ = lean_ctor_get(v_val_2111_, 1);
lean_inc_ref(v_p_2116_);
lean_dec(v_val_2111_);
v___x_2117_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_2116_, v_snd_2094_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec_ref(v_p_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
lean_dec_ref_known(v___x_2117_, 1);
v___x_2118_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2119_ = lean_int_dec_lt(v___x_2118_, v_d_2115_);
lean_dec(v_d_2115_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2121_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2120_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2135_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2135_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2135_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
if (lean_obj_tag(v_a_2122_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; 
lean_del_object(v___x_2096_);
v_a_2126_ = lean_ctor_get(v_a_2122_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v_a_2122_, 1);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v_a_2126_);
v___x_2128_ = v___x_2113_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2126_);
v___x_2128_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v_snd_2094_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2129_);
v___x_2131_ = v___x_2124_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
else
{
lean_object* v_a_2134_; 
lean_del_object(v___x_2124_);
lean_del_object(v___x_2113_);
lean_dec(v_snd_2094_);
v_a_2134_ = lean_ctor_get(v_a_2122_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v_a_2122_, 1);
v_a_2100_ = v_a_2134_;
goto v___jp_2099_;
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_del_object(v___x_2113_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
v_a_2136_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2121_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2121_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_del_object(v___x_2113_);
goto v___jp_2107_;
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_d_2115_);
lean_del_object(v___x_2113_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
v_a_2144_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2117_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2117_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
else
{
lean_dec(v_a_2110_);
goto v___jp_2107_;
}
v___jp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v_a_2100_);
lean_ctor_set(v___x_2096_, 0, v___x_2098_);
v___x_2102_ = v___x_2096_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_a_2100_);
v___x_2102_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
size_t v___x_2103_; size_t v___x_2104_; 
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_add(v_i_2079_, v___x_2103_);
v_i_2079_ = v___x_2104_;
v_b_2080_ = v___x_2102_;
goto _start;
}
}
v___jp_2107_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = lean_nat_add(v_snd_2094_, v___x_2108_);
lean_dec(v_snd_2094_);
v_a_2100_ = v___x_2109_;
goto v___jp_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2155_, lean_object* v_sz_2156_, lean_object* v_i_2157_, lean_object* v_b_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
size_t v_sz_boxed_2170_; size_t v_i_boxed_2171_; lean_object* v_res_2172_; 
v_sz_boxed_2170_ = lean_unbox_usize(v_sz_2156_);
lean_dec(v_sz_2156_);
v_i_boxed_2171_ = lean_unbox_usize(v_i_2157_);
lean_dec(v_i_2157_);
v_res_2172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2155_, v_sz_boxed_2170_, v_i_boxed_2171_, v_b_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v_as_2155_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(lean_object* v_as_2173_, size_t v_sz_2174_, size_t v_i_2175_, lean_object* v_b_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
uint8_t v___x_2188_; 
v___x_2188_ = lean_usize_dec_lt(v_i_2175_, v_sz_2174_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_b_2176_);
return v___x_2189_;
}
else
{
lean_object* v_snd_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2249_; 
v_snd_2190_ = lean_ctor_get(v_b_2176_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_b_2176_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v_b_2176_, 0);
lean_dec(v_unused_2250_);
v___x_2192_ = v_b_2176_;
v_isShared_2193_ = v_isSharedCheck_2249_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_snd_2190_);
lean_dec(v_b_2176_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2249_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v_a_2196_; lean_object* v_a_2206_; 
v___x_2194_ = lean_box(0);
v_a_2206_ = lean_array_uget(v_as_2173_, v_i_2175_);
if (lean_obj_tag(v_a_2206_) == 1)
{
lean_object* v_val_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2248_; 
v_val_2207_ = lean_ctor_get(v_a_2206_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_a_2206_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2209_ = v_a_2206_;
v_isShared_2210_ = v_isSharedCheck_2248_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_val_2207_);
lean_dec(v_a_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2248_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_d_2211_; lean_object* v_p_2212_; lean_object* v___x_2213_; 
v_d_2211_ = lean_ctor_get(v_val_2207_, 0);
lean_inc(v_d_2211_);
v_p_2212_ = lean_ctor_get(v_val_2207_, 1);
lean_inc_ref(v_p_2212_);
lean_dec(v_val_2207_);
v___x_2213_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_2212_, v_snd_2190_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec_ref(v_p_2212_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2214_; uint8_t v___x_2215_; 
lean_dec_ref_known(v___x_2213_, 1);
v___x_2214_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2215_ = lean_int_dec_lt(v___x_2214_, v_d_2211_);
lean_dec(v_d_2211_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2217_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2216_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2231_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2231_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2231_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
if (lean_obj_tag(v_a_2218_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; 
lean_del_object(v___x_2192_);
v_a_2222_ = lean_ctor_get(v_a_2218_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v_a_2218_, 1);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v_a_2222_);
v___x_2224_ = v___x_2209_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2222_);
v___x_2224_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v_snd_2190_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2225_);
v___x_2227_ = v___x_2220_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_object* v_a_2230_; 
lean_del_object(v___x_2220_);
lean_del_object(v___x_2209_);
lean_dec(v_snd_2190_);
v_a_2230_ = lean_ctor_get(v_a_2218_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v_a_2218_, 1);
v_a_2196_ = v_a_2230_;
goto v___jp_2195_;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_del_object(v___x_2209_);
lean_del_object(v___x_2192_);
lean_dec(v_snd_2190_);
v_a_2232_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2217_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2217_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_del_object(v___x_2209_);
goto v___jp_2203_;
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_d_2211_);
lean_del_object(v___x_2209_);
lean_del_object(v___x_2192_);
lean_dec(v_snd_2190_);
v_a_2240_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2213_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2213_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
else
{
lean_dec(v_a_2206_);
goto v___jp_2203_;
}
v___jp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v_a_2196_);
lean_ctor_set(v___x_2192_, 0, v___x_2194_);
v___x_2198_ = v___x_2192_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_a_2196_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
size_t v___x_2199_; size_t v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = ((size_t)1ULL);
v___x_2200_ = lean_usize_add(v_i_2175_, v___x_2199_);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2173_, v_sz_2174_, v___x_2200_, v___x_2198_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
return v___x_2201_;
}
}
v___jp_2203_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_add(v_snd_2190_, v___x_2204_);
lean_dec(v_snd_2190_);
v_a_2196_ = v___x_2205_;
goto v___jp_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2___boxed(lean_object* v_as_2251_, lean_object* v_sz_2252_, lean_object* v_i_2253_, lean_object* v_b_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
size_t v_sz_boxed_2266_; size_t v_i_boxed_2267_; lean_object* v_res_2268_; 
v_sz_boxed_2266_ = lean_unbox_usize(v_sz_2252_);
lean_dec(v_sz_2252_);
v_i_boxed_2267_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_as_2251_, v_sz_boxed_2266_, v_i_boxed_2267_, v_b_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v_as_2251_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(lean_object* v_t_2269_, lean_object* v_init_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_root_2282_; lean_object* v_tail_2283_; lean_object* v___x_2284_; 
v_root_2282_ = lean_ctor_get(v_t_2269_, 0);
v_tail_2283_ = lean_ctor_get(v_t_2269_, 1);
lean_inc(v_init_2270_);
v___x_2284_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2270_, v_root_2282_, v_init_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v_init_2270_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2321_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2321_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2321_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
if (lean_obj_tag(v_a_2285_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; 
v_a_2289_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v_a_2285_, 1);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_a_2289_);
v___x_2291_ = v___x_2287_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; size_t v_sz_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
lean_del_object(v___x_2287_);
v_a_2293_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v_a_2285_, 1);
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v_a_2293_);
v_sz_2296_ = lean_array_size(v_tail_2283_);
v___x_2297_ = ((size_t)0ULL);
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_tail_2283_, v_sz_2296_, v___x_2297_, v___x_2295_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2312_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2312_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2312_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_fst_2303_; 
v_fst_2303_ = lean_ctor_get(v_a_2299_, 0);
if (lean_obj_tag(v_fst_2303_) == 0)
{
lean_object* v_snd_2304_; lean_object* v___x_2306_; 
v_snd_2304_ = lean_ctor_get(v_a_2299_, 1);
lean_inc(v_snd_2304_);
lean_dec(v_a_2299_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v_snd_2304_);
v___x_2306_ = v___x_2301_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_snd_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
else
{
lean_object* v_val_2308_; lean_object* v___x_2310_; 
lean_inc_ref(v_fst_2303_);
lean_dec(v_a_2299_);
v_val_2308_ = lean_ctor_get(v_fst_2303_, 0);
lean_inc(v_val_2308_);
lean_dec_ref_known(v_fst_2303_, 1);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v_val_2308_);
v___x_2310_ = v___x_2301_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_val_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2298_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2298_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
v_a_2322_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2284_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2284_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1___boxed(lean_object* v_t_2330_, lean_object* v_init_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_t_2330_, v_init_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v_t_2330_);
return v_res_2343_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2345_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0));
v___x_2346_ = lean_unsigned_to_nat(2u);
v___x_2347_ = lean_unsigned_to_nat(65u);
v___x_2348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_2349_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2350_ = l_mkPanicMessageWithDecl(v___x_2349_, v___x_2348_, v___x_2347_, v___x_2346_, v___x_2345_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2351_, v_a_2359_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v_vars_2364_; lean_object* v_dvds_2365_; lean_object* v_size_2366_; lean_object* v_size_2367_; uint8_t v___x_2368_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v_vars_2364_ = lean_ctor_get(v_a_2363_, 0);
lean_inc_ref(v_vars_2364_);
v_dvds_2365_ = lean_ctor_get(v_a_2363_, 6);
lean_inc_ref(v_dvds_2365_);
lean_dec(v_a_2363_);
v_size_2366_ = lean_ctor_get(v_vars_2364_, 2);
lean_inc(v_size_2366_);
lean_dec_ref(v_vars_2364_);
v_size_2367_ = lean_ctor_get(v_dvds_2365_, 2);
v___x_2368_ = lean_nat_dec_eq(v_size_2366_, v_size_2367_);
lean_dec(v_size_2366_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_dec_ref(v_dvds_2365_);
v___x_2369_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1);
v___x_2370_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2369_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
return v___x_2370_;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_dvds_2365_, v___x_2371_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec_ref(v_dvds_2365_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2380_; 
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v___x_2372_, 0);
lean_dec(v_unused_2381_);
v___x_2374_ = v___x_2372_;
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
else
{
lean_dec(v___x_2372_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2376_ = lean_box(0);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2376_);
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
v_a_2382_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2372_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2372_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v_a_2390_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2362_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2362_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___boxed(lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec(v_a_2398_);
return v_res_2409_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2411_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_2412_ = lean_unsigned_to_nat(6u);
v___x_2413_ = lean_unsigned_to_nat(81u);
v___x_2414_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2415_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2416_ = l_mkPanicMessageWithDecl(v___x_2415_, v___x_2414_, v___x_2413_, v___x_2412_, v___x_2411_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2418_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2));
v___x_2419_ = lean_unsigned_to_nat(6u);
v___x_2420_ = lean_unsigned_to_nat(79u);
v___x_2421_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2422_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2423_ = l_mkPanicMessageWithDecl(v___x_2422_, v___x_2421_, v___x_2420_, v___x_2419_, v___x_2418_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(lean_object* v_vars_2424_, lean_object* v___x_2425_, lean_object* v_x_2426_, lean_object* v_____s_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_fst_2444_; lean_object* v_snd_2445_; lean_object* v_size_2446_; uint8_t v___x_2447_; 
v_fst_2444_ = lean_ctor_get(v_x_2426_, 0);
v_snd_2445_ = lean_ctor_get(v_x_2426_, 1);
v_size_2446_ = lean_ctor_get(v_vars_2424_, 2);
v___x_2447_ = lean_nat_dec_lt(v_snd_2445_, v_size_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1);
v___x_2449_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2448_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_dec_ref_known(v___x_2449_, 1);
goto v___jp_2439_;
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; uint8_t v___x_2461_; 
v___x_2458_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2425_, v_vars_2424_, v_snd_2445_);
v___x_2459_ = lean_ptr_addr(v_fst_2444_);
v___x_2460_ = lean_ptr_addr(v___x_2458_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_usize_dec_eq(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3);
v___x_2463_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2462_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
return v___x_2463_;
}
else
{
goto v___jp_2439_;
}
}
v___jp_2439_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2440_ = lean_unsigned_to_nat(1u);
v___x_2441_ = lean_nat_add(v_____s_2427_, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(lean_object* v_vars_2464_, lean_object* v___x_2465_, lean_object* v_x_2466_, lean_object* v_____s_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(v_vars_2464_, v___x_2465_, v_x_2466_, v_____s_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec(v_____s_2467_);
lean_dec_ref(v_x_2466_);
lean_dec_ref(v___x_2465_);
lean_dec_ref(v_vars_2464_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2480_, lean_object* v_keys_2481_, lean_object* v_vals_2482_, lean_object* v_i_2483_, lean_object* v_acc_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = lean_array_get_size(v_keys_2481_);
v___x_2497_ = lean_nat_dec_lt(v_i_2483_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec(v_i_2483_);
lean_dec_ref(v_f_2480_);
v___x_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_acc_2484_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
else
{
lean_object* v_k_2500_; lean_object* v_v_2501_; lean_object* v___x_2502_; 
v_k_2500_ = lean_array_fget_borrowed(v_keys_2481_, v_i_2483_);
v_v_2501_ = lean_array_fget_borrowed(v_vals_2482_, v_i_2483_);
lean_inc_ref(v_f_2480_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
lean_inc(v___y_2488_);
lean_inc_ref(v___y_2487_);
lean_inc(v___y_2486_);
lean_inc(v___y_2485_);
lean_inc(v_v_2501_);
lean_inc(v_k_2500_);
v___x_2502_ = lean_apply_14(v_f_2480_, v_acc_2484_, v_k_2500_, v_v_2501_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, lean_box(0));
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
if (lean_obj_tag(v_a_2503_) == 0)
{
lean_dec_ref_known(v_a_2503_, 1);
lean_dec(v_i_2483_);
lean_dec_ref(v_f_2480_);
return v___x_2502_;
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref_known(v___x_2502_, 1);
v_a_2504_ = lean_ctor_get(v_a_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v_a_2503_, 1);
v___x_2505_ = lean_unsigned_to_nat(1u);
v___x_2506_ = lean_nat_add(v_i_2483_, v___x_2505_);
lean_dec(v_i_2483_);
v_i_2483_ = v___x_2506_;
v_acc_2484_ = v_a_2504_;
goto _start;
}
}
else
{
lean_dec(v_i_2483_);
lean_dec_ref(v_f_2480_);
return v___x_2502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2508_, lean_object* v_keys_2509_, lean_object* v_vals_2510_, lean_object* v_i_2511_, lean_object* v_acc_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2508_, v_keys_2509_, v_vals_2510_, v_i_2511_, v_acc_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v_vals_2510_);
lean_dec_ref(v_keys_2509_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2525_, lean_object* v_as_2526_, size_t v_i_2527_, size_t v_stop_2528_, lean_object* v_b_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_a_2542_; lean_object* v___y_2547_; uint8_t v___x_2550_; 
v___x_2550_ = lean_usize_dec_eq(v_i_2527_, v_stop_2528_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_array_uget_borrowed(v_as_2526_, v_i_2527_);
switch(lean_obj_tag(v___x_2551_))
{
case 0:
{
lean_object* v_key_2552_; lean_object* v_val_2553_; lean_object* v___x_2554_; 
v_key_2552_ = lean_ctor_get(v___x_2551_, 0);
v_val_2553_ = lean_ctor_get(v___x_2551_, 1);
lean_inc_ref(v_f_2525_);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2538_);
lean_inc(v___y_2537_);
lean_inc_ref(v___y_2536_);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc(v_val_2553_);
lean_inc(v_key_2552_);
v___x_2554_ = lean_apply_14(v_f_2525_, v_b_2529_, v_key_2552_, v_val_2553_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, lean_box(0));
v___y_2547_ = v___x_2554_;
goto v___jp_2546_;
}
case 1:
{
lean_object* v_node_2555_; lean_object* v___x_2556_; 
v_node_2555_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_node_2555_);
lean_inc_ref(v_f_2525_);
v___x_2556_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2525_, v_node_2555_, v_b_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
v___y_2547_ = v___x_2556_;
goto v___jp_2546_;
}
default: 
{
v_a_2542_ = v_b_2529_;
goto v___jp_2541_;
}
}
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_dec_ref(v_f_2525_);
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_b_2529_);
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
v___jp_2541_:
{
size_t v___x_2543_; size_t v___x_2544_; 
v___x_2543_ = ((size_t)1ULL);
v___x_2544_ = lean_usize_add(v_i_2527_, v___x_2543_);
v_i_2527_ = v___x_2544_;
v_b_2529_ = v_a_2542_;
goto _start;
}
v___jp_2546_:
{
if (lean_obj_tag(v___y_2547_) == 0)
{
lean_object* v_a_2548_; 
v_a_2548_ = lean_ctor_get(v___y_2547_, 0);
if (lean_obj_tag(v_a_2548_) == 0)
{
lean_dec_ref(v_f_2525_);
return v___y_2547_;
}
else
{
lean_object* v_a_2549_; 
lean_inc_ref(v_a_2548_);
lean_dec_ref_known(v___y_2547_, 1);
v_a_2549_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v_a_2548_, 1);
v_a_2542_ = v_a_2549_;
goto v___jp_2541_;
}
}
else
{
lean_dec_ref(v_f_2525_);
return v___y_2547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2559_, lean_object* v_x_2560_, lean_object* v_x_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
if (lean_obj_tag(v_x_2560_) == 0)
{
lean_object* v_es_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2587_; 
v_es_2573_ = lean_ctor_get(v_x_2560_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_x_2560_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2575_ = v_x_2560_;
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_es_2573_);
lean_dec(v_x_2560_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = lean_array_get_size(v_es_2573_);
v___x_2579_ = lean_nat_dec_lt(v___x_2577_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2581_; 
lean_dec_ref(v_es_2573_);
lean_dec_ref(v_f_2559_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set_tag(v___x_2575_, 1);
lean_ctor_set(v___x_2575_, 0, v_x_2561_);
v___x_2581_ = v___x_2575_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_x_2561_);
v___x_2581_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
}
else
{
size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
lean_del_object(v___x_2575_);
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = lean_usize_of_nat(v___x_2578_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2559_, v_es_2573_, v___x_2584_, v___x_2585_, v_x_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec_ref(v_es_2573_);
return v___x_2586_;
}
}
}
else
{
lean_object* v_ks_2588_; lean_object* v_vs_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_ks_2588_ = lean_ctor_get(v_x_2560_, 0);
lean_inc_ref(v_ks_2588_);
v_vs_2589_ = lean_ctor_get(v_x_2560_, 1);
lean_inc_ref(v_vs_2589_);
lean_dec_ref_known(v_x_2560_, 2);
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2559_, v_ks_2588_, v_vs_2589_, v___x_2590_, v_x_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec_ref(v_vs_2589_);
lean_dec_ref(v_ks_2588_);
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2592_, lean_object* v_x_2593_, lean_object* v_x_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2592_, v_x_2593_, v_x_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec(v___y_2595_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2607_, lean_object* v_as_2608_, lean_object* v_i_2609_, lean_object* v_stop_2610_, lean_object* v_b_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
size_t v_i_boxed_2623_; size_t v_stop_boxed_2624_; lean_object* v_res_2625_; 
v_i_boxed_2623_ = lean_unbox_usize(v_i_2609_);
lean_dec(v_i_2609_);
v_stop_boxed_2624_ = lean_unbox_usize(v_stop_2610_);
lean_dec(v_stop_2610_);
v_res_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2607_, v_as_2608_, v_i_boxed_2623_, v_stop_boxed_2624_, v_b_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v_as_2608_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(lean_object* v_f_2626_, lean_object* v_s_2627_, lean_object* v_a_2628_, lean_object* v_b_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2641_, 0, v_a_2628_);
lean_ctor_set(v___x_2641_, 1, v_b_2629_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
lean_inc(v___y_2635_);
lean_inc_ref(v___y_2634_);
lean_inc(v___y_2633_);
lean_inc_ref(v___y_2632_);
lean_inc(v___y_2631_);
lean_inc(v___y_2630_);
v___x_2642_ = lean_apply_13(v_f_2626_, v___x_2641_, v_s_2627_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, lean_box(0));
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2669_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2669_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2669_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
if (lean_obj_tag(v_a_2643_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2657_; 
v_a_2647_ = lean_ctor_get(v_a_2643_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_a_2643_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2649_ = v_a_2643_;
v_isShared_2650_ = v_isSharedCheck_2657_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v_a_2643_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2657_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2654_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2652_);
v___x_2654_ = v___x_2645_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2668_; 
v_a_2658_ = lean_ctor_get(v_a_2643_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_a_2643_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2660_ = v_a_2643_;
v_isShared_2661_ = v_isSharedCheck_2668_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v_a_2643_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2668_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2665_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2663_);
v___x_2665_ = v___x_2645_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
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
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_a_2670_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2642_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2642_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed(lean_object* v_f_2678_, lean_object* v_s_2679_, lean_object* v_a_2680_, lean_object* v_b_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(v_f_2678_, v_s_2679_, v_a_2680_, v_b_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec(v___y_2682_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(lean_object* v_map_2694_, lean_object* v_init_2695_, lean_object* v_f_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___f_2708_; lean_object* v___x_2709_; 
v___f_2708_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed), 15, 1);
lean_closure_set(v___f_2708_, 0, v_f_2696_);
lean_inc_ref(v_map_2694_);
v___x_2709_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v___f_2708_, v_map_2694_, v_init_2695_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2718_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v_a_2714_; lean_object* v___x_2716_; 
v_a_2714_ = lean_ctor_get(v_a_2710_, 0);
lean_inc(v_a_2714_);
lean_dec(v_a_2710_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v_a_2714_);
v___x_2716_ = v___x_2712_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
v_a_2719_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2709_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2709_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___boxed(lean_object* v_map_2727_, lean_object* v_init_2728_, lean_object* v_f_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2727_, v_init_2728_, v_f_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v_map_2727_);
return v_res_2741_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2743_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0));
v___x_2744_ = lean_unsigned_to_nat(2u);
v___x_2745_ = lean_unsigned_to_nat(83u);
v___x_2746_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2747_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2748_ = l_mkPanicMessageWithDecl(v___x_2747_, v___x_2746_, v___x_2745_, v___x_2744_, v___x_2743_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars(lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2749_, v_a_2757_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v_vars_2762_; lean_object* v_varMap_2763_; lean_object* v___x_2764_; lean_object* v___f_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v_vars_2762_ = lean_ctor_get(v_a_2761_, 0);
lean_inc_ref_n(v_vars_2762_, 2);
v_varMap_2763_ = lean_ctor_get(v_a_2761_, 1);
lean_inc_ref(v_varMap_2763_);
lean_dec(v_a_2761_);
v___x_2764_ = l_Lean_instInhabitedExpr;
v___f_2765_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2765_, 0, v_vars_2762_);
lean_closure_set(v___f_2765_, 1, v___x_2764_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_varMap_2763_, v___x_2766_, v___f_2765_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
lean_dec_ref(v_varMap_2763_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2780_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2780_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2780_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v_size_2772_; uint8_t v___x_2773_; 
v_size_2772_ = lean_ctor_get(v_vars_2762_, 2);
lean_inc(v_size_2772_);
lean_dec_ref(v_vars_2762_);
v___x_2773_ = lean_nat_dec_eq(v_size_2772_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec(v_size_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_del_object(v___x_2770_);
v___x_2774_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1);
v___x_2775_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2774_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
return v___x_2775_;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2776_ = lean_box(0);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2776_);
v___x_2778_ = v___x_2770_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v_vars_2762_);
v_a_2781_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2767_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2767_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
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
v_a_2789_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2760_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2760_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___boxed(lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec(v_a_2797_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(lean_object* v_00_u03c3_2809_, lean_object* v_00_u03b2_2810_, lean_object* v_map_2811_, lean_object* v_init_2812_, lean_object* v_f_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2811_, v_init_2812_, v_f_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___boxed(lean_object* v_00_u03c3_2826_, lean_object* v_00_u03b2_2827_, lean_object* v_map_2828_, lean_object* v_init_2829_, lean_object* v_f_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(v_00_u03c3_2826_, v_00_u03b2_2827_, v_map_2828_, v_init_2829_, v_f_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v_map_2828_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(lean_object* v_map_2843_, lean_object* v_f_2844_, lean_object* v_init_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2844_, v_map_2843_, v_init_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_map_2858_, lean_object* v_f_2859_, lean_object* v_init_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(v_map_2858_, v_f_2859_, v_init_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
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
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(lean_object* v_00_u03c3_2873_, lean_object* v_00_u03c3_2874_, lean_object* v_00_u03b2_2875_, lean_object* v_map_2876_, lean_object* v_f_2877_, lean_object* v_init_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2877_, v_map_2876_, v_init_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_2891_ = _args[0];
lean_object* v_00_u03c3_2892_ = _args[1];
lean_object* v_00_u03b2_2893_ = _args[2];
lean_object* v_map_2894_ = _args[3];
lean_object* v_f_2895_ = _args[4];
lean_object* v_init_2896_ = _args[5];
lean_object* v___y_2897_ = _args[6];
lean_object* v___y_2898_ = _args[7];
lean_object* v___y_2899_ = _args[8];
lean_object* v___y_2900_ = _args[9];
lean_object* v___y_2901_ = _args[10];
lean_object* v___y_2902_ = _args[11];
lean_object* v___y_2903_ = _args[12];
lean_object* v___y_2904_ = _args[13];
lean_object* v___y_2905_ = _args[14];
lean_object* v___y_2906_ = _args[15];
lean_object* v___y_2907_ = _args[16];
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(v_00_u03c3_2891_, v_00_u03c3_2892_, v_00_u03b2_2893_, v_map_2894_, v_f_2895_, v_init_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec(v___y_2897_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2909_, lean_object* v_00_u03c3_2910_, lean_object* v_00_u03b1_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_f_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2913_, v_x_2914_, v_x_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_2928_ = _args[0];
lean_object* v_00_u03c3_2929_ = _args[1];
lean_object* v_00_u03b1_2930_ = _args[2];
lean_object* v_00_u03b2_2931_ = _args[3];
lean_object* v_f_2932_ = _args[4];
lean_object* v_x_2933_ = _args[5];
lean_object* v_x_2934_ = _args[6];
lean_object* v___y_2935_ = _args[7];
lean_object* v___y_2936_ = _args[8];
lean_object* v___y_2937_ = _args[9];
lean_object* v___y_2938_ = _args[10];
lean_object* v___y_2939_ = _args[11];
lean_object* v___y_2940_ = _args[12];
lean_object* v___y_2941_ = _args[13];
lean_object* v___y_2942_ = _args[14];
lean_object* v___y_2943_ = _args[15];
lean_object* v___y_2944_ = _args[16];
lean_object* v___y_2945_ = _args[17];
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(v_00_u03c3_2928_, v_00_u03c3_2929_, v_00_u03b1_2930_, v_00_u03b2_2931_, v_f_2932_, v_x_2933_, v_x_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec(v___y_2935_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2947_, lean_object* v_00_u03b2_2948_, lean_object* v_00_u03c3_2949_, lean_object* v_00_u03c3_2950_, lean_object* v_f_2951_, lean_object* v_as_2952_, size_t v_i_2953_, size_t v_stop_2954_, lean_object* v_b_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2951_, v_as_2952_, v_i_2953_, v_stop_2954_, v_b_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03b1_2968_ = _args[0];
lean_object* v_00_u03b2_2969_ = _args[1];
lean_object* v_00_u03c3_2970_ = _args[2];
lean_object* v_00_u03c3_2971_ = _args[3];
lean_object* v_f_2972_ = _args[4];
lean_object* v_as_2973_ = _args[5];
lean_object* v_i_2974_ = _args[6];
lean_object* v_stop_2975_ = _args[7];
lean_object* v_b_2976_ = _args[8];
lean_object* v___y_2977_ = _args[9];
lean_object* v___y_2978_ = _args[10];
lean_object* v___y_2979_ = _args[11];
lean_object* v___y_2980_ = _args[12];
lean_object* v___y_2981_ = _args[13];
lean_object* v___y_2982_ = _args[14];
lean_object* v___y_2983_ = _args[15];
lean_object* v___y_2984_ = _args[16];
lean_object* v___y_2985_ = _args[17];
lean_object* v___y_2986_ = _args[18];
lean_object* v___y_2987_ = _args[19];
_start:
{
size_t v_i_boxed_2988_; size_t v_stop_boxed_2989_; lean_object* v_res_2990_; 
v_i_boxed_2988_ = lean_unbox_usize(v_i_2974_);
lean_dec(v_i_2974_);
v_stop_boxed_2989_ = lean_unbox_usize(v_stop_2975_);
lean_dec(v_stop_2975_);
v_res_2990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2968_, v_00_u03b2_2969_, v_00_u03c3_2970_, v_00_u03c3_2971_, v_f_2972_, v_as_2973_, v_i_boxed_2988_, v_stop_boxed_2989_, v_b_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v_as_2973_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2991_, lean_object* v_00_u03c3_2992_, lean_object* v_00_u03b1_2993_, lean_object* v_00_u03b2_2994_, lean_object* v_f_2995_, lean_object* v_keys_2996_, lean_object* v_vals_2997_, lean_object* v_heq_2998_, lean_object* v_i_2999_, lean_object* v_acc_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2995_, v_keys_2996_, v_vals_2997_, v_i_2999_, v_acc_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_3013_ = _args[0];
lean_object* v_00_u03c3_3014_ = _args[1];
lean_object* v_00_u03b1_3015_ = _args[2];
lean_object* v_00_u03b2_3016_ = _args[3];
lean_object* v_f_3017_ = _args[4];
lean_object* v_keys_3018_ = _args[5];
lean_object* v_vals_3019_ = _args[6];
lean_object* v_heq_3020_ = _args[7];
lean_object* v_i_3021_ = _args[8];
lean_object* v_acc_3022_ = _args[9];
lean_object* v___y_3023_ = _args[10];
lean_object* v___y_3024_ = _args[11];
lean_object* v___y_3025_ = _args[12];
lean_object* v___y_3026_ = _args[13];
lean_object* v___y_3027_ = _args[14];
lean_object* v___y_3028_ = _args[15];
lean_object* v___y_3029_ = _args[16];
lean_object* v___y_3030_ = _args[17];
lean_object* v___y_3031_ = _args[18];
lean_object* v___y_3032_ = _args[19];
lean_object* v___y_3033_ = _args[20];
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3013_, v_00_u03c3_3014_, v_00_u03b1_3015_, v_00_u03b2_3016_, v_f_3017_, v_keys_3018_, v_vals_3019_, v_heq_3020_, v_i_3021_, v_acc_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v_vals_3019_);
lean_dec_ref(v_keys_3018_);
return v_res_3034_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(lean_object* v_a_3035_, lean_object* v_x_3036_){
_start:
{
if (lean_obj_tag(v_x_3036_) == 0)
{
uint8_t v___x_3037_; 
v___x_3037_ = 0;
return v___x_3037_;
}
else
{
lean_object* v_head_3038_; lean_object* v_tail_3039_; uint8_t v___x_3040_; 
v_head_3038_ = lean_ctor_get(v_x_3036_, 0);
v_tail_3039_ = lean_ctor_get(v_x_3036_, 1);
v___x_3040_ = lean_nat_dec_eq(v_a_3035_, v_head_3038_);
if (v___x_3040_ == 0)
{
v_x_3036_ = v_tail_3039_;
goto _start;
}
else
{
return v___x_3040_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0___boxed(lean_object* v_a_3042_, lean_object* v_x_3043_){
_start:
{
uint8_t v_res_3044_; lean_object* v_r_3045_; 
v_res_3044_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_a_3042_, v_x_3043_);
lean_dec(v_x_3043_);
lean_dec(v_a_3042_);
v_r_3045_ = lean_box(v_res_3044_);
return v_r_3045_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_3049_ = lean_unsigned_to_nat(6u);
v___x_3050_ = lean_unsigned_to_nat(94u);
v___x_3051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3052_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3053_ = l_mkPanicMessageWithDecl(v___x_3052_, v___x_3051_, v___x_3050_, v___x_3049_, v___x_3048_);
return v___x_3053_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3));
v___x_3056_ = lean_unsigned_to_nat(6u);
v___x_3057_ = lean_unsigned_to_nat(91u);
v___x_3058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3059_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3060_ = l_mkPanicMessageWithDecl(v___x_3059_, v___x_3058_, v___x_3057_, v___x_3056_, v___x_3055_);
return v___x_3060_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5));
v___x_3063_ = lean_unsigned_to_nat(6u);
v___x_3064_ = lean_unsigned_to_nat(92u);
v___x_3065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3066_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3067_ = l_mkPanicMessageWithDecl(v___x_3066_, v___x_3065_, v___x_3064_, v___x_3063_, v___x_3062_);
return v___x_3067_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7));
v___x_3070_ = lean_unsigned_to_nat(6u);
v___x_3071_ = lean_unsigned_to_nat(93u);
v___x_3072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3073_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3074_ = l_mkPanicMessageWithDecl(v___x_3073_, v___x_3072_, v___x_3071_, v___x_3070_, v___x_3069_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(lean_object* v_a_3075_, lean_object* v_as_3076_, size_t v_sz_3077_, size_t v_i_3078_, lean_object* v_b_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_usize_dec_lt(v_i_3078_, v_sz_3077_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; 
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_b_3079_);
return v___x_3092_;
}
else
{
lean_object* v_snd_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3149_; 
v_snd_3093_ = lean_ctor_get(v_b_3079_, 1);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_b_3079_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v_b_3079_, 0);
lean_dec(v_unused_3150_);
v___x_3095_ = v_b_3079_;
v_isShared_3096_ = v_isSharedCheck_3149_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_snd_3093_);
lean_dec(v_b_3079_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3149_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v_a_3099_; lean_object* v___y_3110_; lean_object* v_a_3133_; 
v___x_3097_ = lean_box(0);
v_a_3133_ = lean_array_uget_borrowed(v_as_3076_, v_i_3078_);
if (lean_obj_tag(v_a_3133_) == 1)
{
lean_object* v_val_3134_; lean_object* v_p_3135_; uint8_t v___x_3136_; 
v_val_3134_ = lean_ctor_get(v_a_3133_, 0);
v_p_3135_ = lean_ctor_get(v_val_3134_, 0);
v___x_3136_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3135_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3138_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3137_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
v___y_3110_ = v___x_3138_;
goto v___jp_3109_;
}
else
{
uint8_t v___x_3139_; 
v___x_3139_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3135_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3141_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3140_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
v___y_3110_ = v___x_3141_;
goto v___jp_3109_;
}
else
{
lean_object* v_elimStack_3142_; uint8_t v___x_3143_; 
v_elimStack_3142_ = lean_ctor_get(v_a_3075_, 11);
v___x_3143_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3093_, v_elimStack_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3145_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3144_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
v___y_3110_ = v___x_3145_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3146_ = l_Int_Internal_Linear_Poly_coeff(v_p_3135_, v_snd_3093_);
v___x_3147_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3148_ = lean_int_dec_eq(v___x_3146_, v___x_3147_);
lean_dec(v___x_3146_);
if (v___x_3148_ == 0)
{
if (v___x_3143_ == 0)
{
goto v___jp_3130_;
}
else
{
goto v___jp_3106_;
}
}
else
{
goto v___jp_3130_;
}
}
}
}
}
else
{
goto v___jp_3106_;
}
v___jp_3098_:
{
lean_object* v___x_3101_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 1, v_a_3099_);
lean_ctor_set(v___x_3095_, 0, v___x_3097_);
v___x_3101_ = v___x_3095_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_a_3099_);
v___x_3101_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
size_t v___x_3102_; size_t v___x_3103_; 
v___x_3102_ = ((size_t)1ULL);
v___x_3103_ = lean_usize_add(v_i_3078_, v___x_3102_);
v_i_3078_ = v___x_3103_;
v_b_3079_ = v___x_3101_;
goto _start;
}
}
v___jp_3106_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_unsigned_to_nat(1u);
v___x_3108_ = lean_nat_add(v_snd_3093_, v___x_3107_);
lean_dec(v_snd_3093_);
v_a_3099_ = v___x_3108_;
goto v___jp_3098_;
}
v___jp_3109_:
{
if (lean_obj_tag(v___y_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3121_; 
v_a_3111_ = lean_ctor_get(v___y_3110_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___y_3110_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3113_ = v___y_3110_;
v_isShared_3114_ = v_isSharedCheck_3121_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___y_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3121_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
if (lean_obj_tag(v_a_3111_) == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
lean_del_object(v___x_3095_);
v___x_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3115_, 0, v_a_3111_);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v_snd_3093_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3116_);
v___x_3118_ = v___x_3113_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
else
{
lean_object* v_a_3120_; 
lean_del_object(v___x_3113_);
lean_dec(v_snd_3093_);
v_a_3120_ = lean_ctor_get(v_a_3111_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v_a_3111_, 1);
v_a_3099_ = v_a_3120_;
goto v___jp_3098_;
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_del_object(v___x_3095_);
lean_dec(v_snd_3093_);
v_a_3122_ = lean_ctor_get(v___y_3110_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___y_3110_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___y_3110_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___y_3110_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
v___jp_3130_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3132_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3131_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
v___y_3110_ = v___x_3132_;
goto v___jp_3109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_a_3151_, lean_object* v_as_3152_, lean_object* v_sz_3153_, lean_object* v_i_3154_, lean_object* v_b_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
size_t v_sz_boxed_3167_; size_t v_i_boxed_3168_; lean_object* v_res_3169_; 
v_sz_boxed_3167_ = lean_unbox_usize(v_sz_3153_);
lean_dec(v_sz_3153_);
v_i_boxed_3168_ = lean_unbox_usize(v_i_3154_);
lean_dec(v_i_3154_);
v_res_3169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3151_, v_as_3152_, v_sz_boxed_3167_, v_i_boxed_3168_, v_b_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v_as_3152_);
lean_dec_ref(v_a_3151_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(lean_object* v_a_3170_, lean_object* v_as_3171_, size_t v_sz_3172_, size_t v_i_3173_, lean_object* v_b_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_usize_dec_lt(v_i_3173_, v_sz_3172_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_b_3174_);
return v___x_3187_;
}
else
{
lean_object* v_snd_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3244_; 
v_snd_3188_ = lean_ctor_get(v_b_3174_, 1);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_b_3174_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v_b_3174_, 0);
lean_dec(v_unused_3245_);
v___x_3190_ = v_b_3174_;
v_isShared_3191_ = v_isSharedCheck_3244_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_snd_3188_);
lean_dec(v_b_3174_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3244_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3192_; lean_object* v_a_3194_; lean_object* v___y_3205_; lean_object* v_a_3228_; 
v___x_3192_ = lean_box(0);
v_a_3228_ = lean_array_uget_borrowed(v_as_3171_, v_i_3173_);
if (lean_obj_tag(v_a_3228_) == 1)
{
lean_object* v_val_3229_; lean_object* v_p_3230_; uint8_t v___x_3231_; 
v_val_3229_ = lean_ctor_get(v_a_3228_, 0);
v_p_3230_ = lean_ctor_get(v_val_3229_, 0);
v___x_3231_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3233_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3232_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
v___y_3205_ = v___x_3233_;
goto v___jp_3204_;
}
else
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3230_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3236_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3235_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
v___y_3205_ = v___x_3236_;
goto v___jp_3204_;
}
else
{
lean_object* v_elimStack_3237_; uint8_t v___x_3238_; 
v_elimStack_3237_ = lean_ctor_get(v_a_3170_, 11);
v___x_3238_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3188_, v_elimStack_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3240_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3239_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
v___y_3205_ = v___x_3240_;
goto v___jp_3204_;
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3241_ = l_Int_Internal_Linear_Poly_coeff(v_p_3230_, v_snd_3188_);
v___x_3242_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3243_ = lean_int_dec_eq(v___x_3241_, v___x_3242_);
lean_dec(v___x_3241_);
if (v___x_3243_ == 0)
{
if (v___x_3238_ == 0)
{
goto v___jp_3225_;
}
else
{
goto v___jp_3201_;
}
}
else
{
goto v___jp_3225_;
}
}
}
}
}
else
{
goto v___jp_3201_;
}
v___jp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 1, v_a_3194_);
lean_ctor_set(v___x_3190_, 0, v___x_3192_);
v___x_3196_ = v___x_3190_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_a_3194_);
v___x_3196_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
size_t v___x_3197_; size_t v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = ((size_t)1ULL);
v___x_3198_ = lean_usize_add(v_i_3173_, v___x_3197_);
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3170_, v_as_3171_, v_sz_3172_, v___x_3198_, v___x_3196_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
return v___x_3199_;
}
}
v___jp_3201_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_unsigned_to_nat(1u);
v___x_3203_ = lean_nat_add(v_snd_3188_, v___x_3202_);
lean_dec(v_snd_3188_);
v_a_3194_ = v___x_3203_;
goto v___jp_3193_;
}
v___jp_3204_:
{
if (lean_obj_tag(v___y_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3216_; 
v_a_3206_ = lean_ctor_get(v___y_3205_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___y_3205_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3208_ = v___y_3205_;
v_isShared_3209_ = v_isSharedCheck_3216_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___y_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3216_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
if (lean_obj_tag(v_a_3206_) == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
lean_del_object(v___x_3190_);
v___x_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_a_3206_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
lean_ctor_set(v___x_3211_, 1, v_snd_3188_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3211_);
v___x_3213_ = v___x_3208_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
else
{
lean_object* v_a_3215_; 
lean_del_object(v___x_3208_);
lean_dec(v_snd_3188_);
v_a_3215_ = lean_ctor_get(v_a_3206_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v_a_3206_, 1);
v_a_3194_ = v_a_3215_;
goto v___jp_3193_;
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_del_object(v___x_3190_);
lean_dec(v_snd_3188_);
v_a_3217_ = lean_ctor_get(v___y_3205_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___y_3205_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___y_3205_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___y_3205_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
v___jp_3225_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3227_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3226_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
v___y_3205_ = v___x_3227_;
goto v___jp_3204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3___boxed(lean_object* v_a_3246_, lean_object* v_as_3247_, lean_object* v_sz_3248_, lean_object* v_i_3249_, lean_object* v_b_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
size_t v_sz_boxed_3262_; size_t v_i_boxed_3263_; lean_object* v_res_3264_; 
v_sz_boxed_3262_ = lean_unbox_usize(v_sz_3248_);
lean_dec(v_sz_3248_);
v_i_boxed_3263_ = lean_unbox_usize(v_i_3249_);
lean_dec(v_i_3249_);
v_res_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3246_, v_as_3247_, v_sz_boxed_3262_, v_i_boxed_3263_, v_b_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v_as_3247_);
lean_dec_ref(v_a_3246_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(lean_object* v_init_3265_, lean_object* v_a_3266_, lean_object* v_n_3267_, lean_object* v_b_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
if (lean_obj_tag(v_n_3267_) == 0)
{
lean_object* v_cs_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; size_t v_sz_3283_; size_t v___x_3284_; lean_object* v___x_3285_; 
v_cs_3280_ = lean_ctor_get(v_n_3267_, 0);
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v_b_3268_);
v_sz_3283_ = lean_array_size(v_cs_3280_);
v___x_3284_ = ((size_t)0ULL);
v___x_3285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3265_, v_a_3266_, v_cs_3280_, v_sz_3283_, v___x_3284_, v___x_3282_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3300_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3300_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3300_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v_fst_3290_; 
v_fst_3290_ = lean_ctor_get(v_a_3286_, 0);
if (lean_obj_tag(v_fst_3290_) == 0)
{
lean_object* v_snd_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
v_snd_3291_ = lean_ctor_get(v_a_3286_, 1);
lean_inc(v_snd_3291_);
lean_dec(v_a_3286_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v_snd_3291_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3292_);
v___x_3294_ = v___x_3288_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
else
{
lean_object* v_val_3296_; lean_object* v___x_3298_; 
lean_inc_ref(v_fst_3290_);
lean_dec(v_a_3286_);
v_val_3296_ = lean_ctor_get(v_fst_3290_, 0);
lean_inc(v_val_3296_);
lean_dec_ref_known(v_fst_3290_, 1);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v_val_3296_);
v___x_3298_ = v___x_3288_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_val_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
v_a_3301_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3285_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3285_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
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
lean_object* v_vs_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; size_t v_sz_3312_; size_t v___x_3313_; lean_object* v___x_3314_; 
v_vs_3309_ = lean_ctor_get(v_n_3267_, 0);
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v_b_3268_);
v_sz_3312_ = lean_array_size(v_vs_3309_);
v___x_3313_ = ((size_t)0ULL);
v___x_3314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3266_, v_vs_3309_, v_sz_3312_, v___x_3313_, v___x_3311_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3329_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3317_ = v___x_3314_;
v_isShared_3318_ = v_isSharedCheck_3329_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3314_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3329_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v_fst_3319_; 
v_fst_3319_ = lean_ctor_get(v_a_3315_, 0);
if (lean_obj_tag(v_fst_3319_) == 0)
{
lean_object* v_snd_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
v_snd_3320_ = lean_ctor_get(v_a_3315_, 1);
lean_inc(v_snd_3320_);
lean_dec(v_a_3315_);
v___x_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_snd_3320_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3321_);
v___x_3323_ = v___x_3317_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
else
{
lean_object* v_val_3325_; lean_object* v___x_3327_; 
lean_inc_ref(v_fst_3319_);
lean_dec(v_a_3315_);
v_val_3325_ = lean_ctor_get(v_fst_3319_, 0);
lean_inc(v_val_3325_);
lean_dec_ref_known(v_fst_3319_, 1);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v_val_3325_);
v___x_3327_ = v___x_3317_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_val_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_a_3330_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3314_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3314_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(lean_object* v_init_3338_, lean_object* v_a_3339_, lean_object* v_as_3340_, size_t v_sz_3341_, size_t v_i_3342_, lean_object* v_b_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_usize_dec_lt(v_i_3342_, v_sz_3341_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_b_3343_);
return v___x_3356_;
}
else
{
lean_object* v_snd_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3391_; 
v_snd_3357_ = lean_ctor_get(v_b_3343_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_b_3343_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; 
v_unused_3392_ = lean_ctor_get(v_b_3343_, 0);
lean_dec(v_unused_3392_);
v___x_3359_ = v_b_3343_;
v_isShared_3360_ = v_isSharedCheck_3391_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_snd_3357_);
lean_dec(v_b_3343_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3391_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_a_3361_; lean_object* v___x_3362_; 
v_a_3361_ = lean_array_uget_borrowed(v_as_3340_, v_i_3342_);
lean_inc(v_snd_3357_);
v___x_3362_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3338_, v_a_3339_, v_a_3361_, v_snd_3357_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3382_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3382_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3382_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
if (lean_obj_tag(v_a_3363_) == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3367_, 0, v_a_3363_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3367_);
v___x_3369_ = v___x_3359_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_snd_3357_);
v___x_3369_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3369_);
v___x_3371_ = v___x_3365_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_del_object(v___x_3365_);
lean_dec(v_snd_3357_);
v_a_3374_ = lean_ctor_get(v_a_3363_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v_a_3363_, 1);
v___x_3375_ = lean_box(0);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v_a_3374_);
lean_ctor_set(v___x_3359_, 0, v___x_3375_);
v___x_3377_ = v___x_3359_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_a_3374_);
v___x_3377_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
size_t v___x_3378_; size_t v___x_3379_; 
v___x_3378_ = ((size_t)1ULL);
v___x_3379_ = lean_usize_add(v_i_3342_, v___x_3378_);
v_i_3342_ = v___x_3379_;
v_b_3343_ = v___x_3377_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_del_object(v___x_3359_);
lean_dec(v_snd_3357_);
v_a_3383_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3362_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3362_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_3393_ = _args[0];
lean_object* v_a_3394_ = _args[1];
lean_object* v_as_3395_ = _args[2];
lean_object* v_sz_3396_ = _args[3];
lean_object* v_i_3397_ = _args[4];
lean_object* v_b_3398_ = _args[5];
lean_object* v___y_3399_ = _args[6];
lean_object* v___y_3400_ = _args[7];
lean_object* v___y_3401_ = _args[8];
lean_object* v___y_3402_ = _args[9];
lean_object* v___y_3403_ = _args[10];
lean_object* v___y_3404_ = _args[11];
lean_object* v___y_3405_ = _args[12];
lean_object* v___y_3406_ = _args[13];
lean_object* v___y_3407_ = _args[14];
lean_object* v___y_3408_ = _args[15];
lean_object* v___y_3409_ = _args[16];
_start:
{
size_t v_sz_boxed_3410_; size_t v_i_boxed_3411_; lean_object* v_res_3412_; 
v_sz_boxed_3410_ = lean_unbox_usize(v_sz_3396_);
lean_dec(v_sz_3396_);
v_i_boxed_3411_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_res_3412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3393_, v_a_3394_, v_as_3395_, v_sz_boxed_3410_, v_i_boxed_3411_, v_b_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v_as_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_init_3393_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1___boxed(lean_object* v_init_3413_, lean_object* v_a_3414_, lean_object* v_n_3415_, lean_object* v_b_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3413_, v_a_3414_, v_n_3415_, v_b_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v_n_3415_);
lean_dec_ref(v_a_3414_);
lean_dec(v_init_3413_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(lean_object* v_a_3429_, lean_object* v_as_3430_, size_t v_sz_3431_, size_t v_i_3432_, lean_object* v_b_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_usize_dec_lt(v_i_3432_, v_sz_3431_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_b_3433_);
return v___x_3446_;
}
else
{
lean_object* v_snd_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3510_; 
v_snd_3447_ = lean_ctor_get(v_b_3433_, 1);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_b_3433_);
if (v_isSharedCheck_3510_ == 0)
{
lean_object* v_unused_3511_; 
v_unused_3511_ = lean_ctor_get(v_b_3433_, 0);
lean_dec(v_unused_3511_);
v___x_3449_ = v_b_3433_;
v_isShared_3450_ = v_isSharedCheck_3510_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_snd_3447_);
lean_dec(v_b_3433_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3510_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v_a_3453_; lean_object* v___y_3464_; lean_object* v_a_3494_; 
v___x_3451_ = lean_box(0);
v_a_3494_ = lean_array_uget_borrowed(v_as_3430_, v_i_3432_);
if (lean_obj_tag(v_a_3494_) == 1)
{
lean_object* v_val_3495_; lean_object* v_p_3496_; uint8_t v___x_3497_; 
v_val_3495_ = lean_ctor_get(v_a_3494_, 0);
v_p_3496_ = lean_ctor_get(v_val_3495_, 0);
v___x_3497_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3499_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3498_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
v___y_3464_ = v___x_3499_;
goto v___jp_3463_;
}
else
{
uint8_t v___x_3500_; 
v___x_3500_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3496_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3502_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3501_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
v___y_3464_ = v___x_3502_;
goto v___jp_3463_;
}
else
{
lean_object* v_elimStack_3503_; uint8_t v___x_3504_; 
v_elimStack_3503_ = lean_ctor_get(v_a_3429_, 11);
v___x_3504_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3447_, v_elimStack_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3506_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3505_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
v___y_3464_ = v___x_3506_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3507_ = l_Int_Internal_Linear_Poly_coeff(v_p_3496_, v_snd_3447_);
v___x_3508_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3509_ = lean_int_dec_eq(v___x_3507_, v___x_3508_);
lean_dec(v___x_3507_);
if (v___x_3509_ == 0)
{
if (v___x_3504_ == 0)
{
goto v___jp_3491_;
}
else
{
goto v___jp_3460_;
}
}
else
{
goto v___jp_3491_;
}
}
}
}
}
else
{
goto v___jp_3460_;
}
v___jp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 1, v_a_3453_);
lean_ctor_set(v___x_3449_, 0, v___x_3451_);
v___x_3455_ = v___x_3449_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_a_3453_);
v___x_3455_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
size_t v___x_3456_; size_t v___x_3457_; 
v___x_3456_ = ((size_t)1ULL);
v___x_3457_ = lean_usize_add(v_i_3432_, v___x_3456_);
v_i_3432_ = v___x_3457_;
v_b_3433_ = v___x_3455_;
goto _start;
}
}
v___jp_3460_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = lean_unsigned_to_nat(1u);
v___x_3462_ = lean_nat_add(v_snd_3447_, v___x_3461_);
lean_dec(v_snd_3447_);
v_a_3453_ = v___x_3462_;
goto v___jp_3452_;
}
v___jp_3463_:
{
if (lean_obj_tag(v___y_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3482_; 
v_a_3465_ = lean_ctor_get(v___y_3464_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___y_3464_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3467_ = v___y_3464_;
v_isShared_3468_ = v_isSharedCheck_3482_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___y_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3482_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
if (lean_obj_tag(v_a_3465_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3480_; 
lean_del_object(v___x_3449_);
v_a_3469_ = lean_ctor_get(v_a_3465_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_a_3465_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3471_ = v_a_3465_;
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v_a_3465_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set_tag(v___x_3471_, 1);
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v_snd_3447_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3475_);
v___x_3477_ = v___x_3467_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v_a_3481_; 
lean_del_object(v___x_3467_);
lean_dec(v_snd_3447_);
v_a_3481_ = lean_ctor_get(v_a_3465_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v_a_3465_, 1);
v_a_3453_ = v_a_3481_;
goto v___jp_3452_;
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_del_object(v___x_3449_);
lean_dec(v_snd_3447_);
v_a_3483_ = lean_ctor_get(v___y_3464_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___y_3464_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___y_3464_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___y_3464_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
v___jp_3491_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3493_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3492_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
v___y_3464_ = v___x_3493_;
goto v___jp_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5___boxed(lean_object* v_a_3512_, lean_object* v_as_3513_, lean_object* v_sz_3514_, lean_object* v_i_3515_, lean_object* v_b_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
size_t v_sz_boxed_3528_; size_t v_i_boxed_3529_; lean_object* v_res_3530_; 
v_sz_boxed_3528_ = lean_unbox_usize(v_sz_3514_);
lean_dec(v_sz_3514_);
v_i_boxed_3529_ = lean_unbox_usize(v_i_3515_);
lean_dec(v_i_3515_);
v_res_3530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3512_, v_as_3513_, v_sz_boxed_3528_, v_i_boxed_3529_, v_b_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v_as_3513_);
lean_dec_ref(v_a_3512_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(lean_object* v_a_3531_, lean_object* v_as_3532_, size_t v_sz_3533_, size_t v_i_3534_, lean_object* v_b_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
uint8_t v___x_3547_; 
v___x_3547_ = lean_usize_dec_lt(v_i_3534_, v_sz_3533_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v_b_3535_);
return v___x_3548_;
}
else
{
lean_object* v_snd_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3612_; 
v_snd_3549_ = lean_ctor_get(v_b_3535_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_b_3535_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v_b_3535_, 0);
lean_dec(v_unused_3613_);
v___x_3551_ = v_b_3535_;
v_isShared_3552_ = v_isSharedCheck_3612_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_snd_3549_);
lean_dec(v_b_3535_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3612_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v_a_3555_; lean_object* v___y_3566_; lean_object* v_a_3596_; 
v___x_3553_ = lean_box(0);
v_a_3596_ = lean_array_uget_borrowed(v_as_3532_, v_i_3534_);
if (lean_obj_tag(v_a_3596_) == 1)
{
lean_object* v_val_3597_; lean_object* v_p_3598_; uint8_t v___x_3599_; 
v_val_3597_ = lean_ctor_get(v_a_3596_, 0);
v_p_3598_ = lean_ctor_get(v_val_3597_, 0);
v___x_3599_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3601_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3600_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
v___y_3566_ = v___x_3601_;
goto v___jp_3565_;
}
else
{
uint8_t v___x_3602_; 
v___x_3602_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3598_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3604_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3603_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
v___y_3566_ = v___x_3604_;
goto v___jp_3565_;
}
else
{
lean_object* v_elimStack_3605_; uint8_t v___x_3606_; 
v_elimStack_3605_ = lean_ctor_get(v_a_3531_, 11);
v___x_3606_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3549_, v_elimStack_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3608_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3607_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
v___y_3566_ = v___x_3608_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v___x_3609_ = l_Int_Internal_Linear_Poly_coeff(v_p_3598_, v_snd_3549_);
v___x_3610_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3611_ = lean_int_dec_eq(v___x_3609_, v___x_3610_);
lean_dec(v___x_3609_);
if (v___x_3611_ == 0)
{
if (v___x_3606_ == 0)
{
goto v___jp_3593_;
}
else
{
goto v___jp_3562_;
}
}
else
{
goto v___jp_3593_;
}
}
}
}
}
else
{
goto v___jp_3562_;
}
v___jp_3554_:
{
lean_object* v___x_3557_; 
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 1, v_a_3555_);
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3557_ = v___x_3551_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_a_3555_);
v___x_3557_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
size_t v___x_3558_; size_t v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((size_t)1ULL);
v___x_3559_ = lean_usize_add(v_i_3534_, v___x_3558_);
v___x_3560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3531_, v_as_3532_, v_sz_3533_, v___x_3559_, v___x_3557_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
return v___x_3560_;
}
}
v___jp_3562_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = lean_unsigned_to_nat(1u);
v___x_3564_ = lean_nat_add(v_snd_3549_, v___x_3563_);
lean_dec(v_snd_3549_);
v_a_3555_ = v___x_3564_;
goto v___jp_3554_;
}
v___jp_3565_:
{
if (lean_obj_tag(v___y_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3584_; 
v_a_3567_ = lean_ctor_get(v___y_3566_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___y_3566_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3569_ = v___y_3566_;
v_isShared_3570_ = v_isSharedCheck_3584_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___y_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3584_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
if (lean_obj_tag(v_a_3567_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3582_; 
lean_del_object(v___x_3551_);
v_a_3571_ = lean_ctor_get(v_a_3567_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_a_3567_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3573_ = v_a_3567_;
v_isShared_3574_ = v_isSharedCheck_3582_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v_a_3567_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3582_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set_tag(v___x_3573_, 1);
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
lean_ctor_set(v___x_3577_, 1, v_snd_3549_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3577_);
v___x_3579_ = v___x_3569_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v_a_3583_; 
lean_del_object(v___x_3569_);
lean_dec(v_snd_3549_);
v_a_3583_ = lean_ctor_get(v_a_3567_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v_a_3567_, 1);
v_a_3555_ = v_a_3583_;
goto v___jp_3554_;
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_del_object(v___x_3551_);
lean_dec(v_snd_3549_);
v_a_3585_ = lean_ctor_get(v___y_3566_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___y_3566_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___y_3566_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___y_3566_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
v___jp_3593_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3595_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3594_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
v___y_3566_ = v___x_3595_;
goto v___jp_3565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2___boxed(lean_object* v_a_3614_, lean_object* v_as_3615_, lean_object* v_sz_3616_, lean_object* v_i_3617_, lean_object* v_b_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
size_t v_sz_boxed_3630_; size_t v_i_boxed_3631_; lean_object* v_res_3632_; 
v_sz_boxed_3630_ = lean_unbox_usize(v_sz_3616_);
lean_dec(v_sz_3616_);
v_i_boxed_3631_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_res_3632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3614_, v_as_3615_, v_sz_boxed_3630_, v_i_boxed_3631_, v_b_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v_as_3615_);
lean_dec_ref(v_a_3614_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(lean_object* v_a_3633_, lean_object* v_t_3634_, lean_object* v_init_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v_root_3647_; lean_object* v_tail_3648_; lean_object* v___x_3649_; 
v_root_3647_ = lean_ctor_get(v_t_3634_, 0);
v_tail_3648_ = lean_ctor_get(v_t_3634_, 1);
lean_inc(v_init_3635_);
v___x_3649_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3635_, v_a_3633_, v_root_3647_, v_init_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v_init_3635_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3686_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3686_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3686_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
if (lean_obj_tag(v_a_3650_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; 
v_a_3654_ = lean_ctor_get(v_a_3650_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v_a_3650_, 1);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_a_3654_);
v___x_3656_ = v___x_3652_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; size_t v_sz_3661_; size_t v___x_3662_; lean_object* v___x_3663_; 
lean_del_object(v___x_3652_);
v_a_3658_ = lean_ctor_get(v_a_3650_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v_a_3650_, 1);
v___x_3659_ = lean_box(0);
v___x_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
lean_ctor_set(v___x_3660_, 1, v_a_3658_);
v_sz_3661_ = lean_array_size(v_tail_3648_);
v___x_3662_ = ((size_t)0ULL);
v___x_3663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3633_, v_tail_3648_, v_sz_3661_, v___x_3662_, v___x_3660_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3677_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3677_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3677_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v_fst_3668_; 
v_fst_3668_ = lean_ctor_get(v_a_3664_, 0);
if (lean_obj_tag(v_fst_3668_) == 0)
{
lean_object* v_snd_3669_; lean_object* v___x_3671_; 
v_snd_3669_ = lean_ctor_get(v_a_3664_, 1);
lean_inc(v_snd_3669_);
lean_dec(v_a_3664_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v_snd_3669_);
v___x_3671_ = v___x_3666_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_snd_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
else
{
lean_object* v_val_3673_; lean_object* v___x_3675_; 
lean_inc_ref(v_fst_3668_);
lean_dec(v_a_3664_);
v_val_3673_ = lean_ctor_get(v_fst_3668_, 0);
lean_inc(v_val_3673_);
lean_dec_ref_known(v_fst_3668_, 1);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v_val_3673_);
v___x_3675_ = v___x_3666_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_val_3673_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
v_a_3678_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3663_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3663_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
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
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
v_a_3687_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3649_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3649_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1___boxed(lean_object* v_a_3695_, lean_object* v_t_3696_, lean_object* v_init_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3695_, v_t_3696_, v_init_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v_t_3696_);
lean_dec_ref(v_a_3695_);
return v_res_3709_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3711_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0));
v___x_3712_ = lean_unsigned_to_nat(2u);
v___x_3713_ = lean_unsigned_to_nat(87u);
v___x_3714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3715_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3716_ = l_mkPanicMessageWithDecl(v___x_3715_, v___x_3714_, v___x_3713_, v___x_3712_, v___x_3711_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3717_, v_a_3725_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; lean_object* v_elimEqs_3730_; lean_object* v_vars_3731_; lean_object* v_size_3732_; lean_object* v_size_3733_; uint8_t v___x_3734_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref_known(v___x_3728_, 1);
v_elimEqs_3730_ = lean_ctor_get(v_a_3729_, 10);
lean_inc_ref(v_elimEqs_3730_);
v_vars_3731_ = lean_ctor_get(v_a_3729_, 0);
v_size_3732_ = lean_ctor_get(v_elimEqs_3730_, 2);
v_size_3733_ = lean_ctor_get(v_vars_3731_, 2);
v___x_3734_ = lean_nat_dec_eq(v_size_3732_, v_size_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
lean_dec_ref(v_elimEqs_3730_);
lean_dec(v_a_3729_);
v___x_3735_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1);
v___x_3736_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_3735_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
return v___x_3736_;
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = lean_unsigned_to_nat(0u);
v___x_3738_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3729_, v_elimEqs_3730_, v___x_3737_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
lean_dec_ref(v_elimEqs_3730_);
lean_dec(v_a_3729_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3746_; 
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; 
v_unused_3747_ = lean_ctor_get(v___x_3738_, 0);
lean_dec(v_unused_3747_);
v___x_3740_ = v___x_3738_;
v_isShared_3741_ = v_isSharedCheck_3746_;
goto v_resetjp_3739_;
}
else
{
lean_dec(v___x_3738_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3746_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3744_; 
v___x_3742_ = lean_box(0);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3742_);
v___x_3744_ = v___x_3740_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
v_a_3748_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3738_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3738_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
v_a_3756_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3728_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3728_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___boxed(lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec(v_a_3764_);
return v_res_3775_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3778_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1));
v___x_3779_ = lean_unsigned_to_nat(4u);
v___x_3780_ = lean_unsigned_to_nat(99u);
v___x_3781_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0));
v___x_3782_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3783_ = l_mkPanicMessageWithDecl(v___x_3782_, v___x_3781_, v___x_3780_, v___x_3779_, v___x_3778_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(lean_object* v_as_x27_3784_, lean_object* v_b_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
if (lean_obj_tag(v_as_x27_3784_) == 0)
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v_b_3785_);
return v___x_3797_;
}
else
{
lean_object* v_head_3798_; lean_object* v_tail_3799_; lean_object* v___x_3800_; 
v_head_3798_ = lean_ctor_get(v_as_x27_3784_, 0);
v_tail_3799_ = lean_ctor_get(v_as_x27_3784_, 1);
v___x_3800_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_head_3798_, v___y_3786_, v___y_3794_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; uint8_t v___x_3802_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3800_, 1);
v___x_3802_ = lean_unbox(v_a_3801_);
lean_dec(v_a_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2);
v___x_3804_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_3803_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3815_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3815_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3815_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
if (lean_obj_tag(v_a_3805_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; 
v_a_3809_ = lean_ctor_get(v_a_3805_, 0);
lean_inc(v_a_3809_);
lean_dec_ref_known(v_a_3805_, 1);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v_a_3809_);
v___x_3811_ = v___x_3807_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
else
{
lean_object* v_a_3813_; 
lean_del_object(v___x_3807_);
v_a_3813_ = lean_ctor_get(v_a_3805_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v_a_3805_, 1);
v_as_x27_3784_ = v_tail_3799_;
v_b_3785_ = v_a_3813_;
goto _start;
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
v_a_3816_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3804_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3804_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_box(0);
v_as_x27_3784_ = v_tail_3799_;
v_b_3785_ = v___x_3824_;
goto _start;
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
v_a_3826_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3800_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3800_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___boxed(lean_object* v_as_x27_3834_, lean_object* v_b_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3834_, v_b_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v_as_x27_3834_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3848_, v_a_3856_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v_elimStack_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3859_, 1);
v_elimStack_3861_ = lean_ctor_get(v_a_3860_, 11);
lean_inc(v_elimStack_3861_);
lean_dec(v_a_3860_);
v___x_3862_ = lean_box(0);
v___x_3863_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_elimStack_3861_, v___x_3862_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
lean_dec(v_elimStack_3861_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; 
v_unused_3871_ = lean_ctor_get(v___x_3863_, 0);
lean_dec(v_unused_3871_);
v___x_3865_ = v___x_3863_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_dec(v___x_3863_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 0, v___x_3862_);
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3862_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
else
{
return v___x_3863_;
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_a_3872_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3859_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3859_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack___boxed(lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
lean_dec(v_a_3889_);
lean_dec_ref(v_a_3888_);
lean_dec(v_a_3887_);
lean_dec_ref(v_a_3886_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
lean_dec(v_a_3881_);
lean_dec(v_a_3880_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(lean_object* v_as_3892_, lean_object* v_as_x27_3893_, lean_object* v_b_3894_, lean_object* v_a_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3893_, v_b_3894_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___boxed(lean_object* v_as_3908_, lean_object* v_as_x27_3909_, lean_object* v_b_3910_, lean_object* v_a_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(v_as_3908_, v_as_x27_3909_, v_b_3910_, v_a_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec(v_as_x27_3909_);
lean_dec(v_as_3908_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_3927_, lean_object* v_as_3928_, size_t v_sz_3929_, size_t v_i_3930_, lean_object* v_b_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
uint8_t v___x_3943_; 
v___x_3943_ = lean_usize_dec_lt(v_i_3930_, v_sz_3929_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; 
v___x_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3944_, 0, v_b_3931_);
return v___x_3944_;
}
else
{
lean_object* v_a_3945_; lean_object* v_p_3946_; lean_object* v___x_3947_; 
lean_dec_ref(v_b_3931_);
v_a_3945_ = lean_array_uget_borrowed(v_as_3928_, v_i_3930_);
v_p_3946_ = lean_ctor_get(v_a_3945_, 0);
v___x_3947_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_3946_, v_____s_3927_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v___x_3948_; size_t v___x_3949_; size_t v___x_3950_; 
lean_dec_ref_known(v___x_3947_, 1);
v___x_3948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_3949_ = ((size_t)1ULL);
v___x_3950_ = lean_usize_add(v_i_3930_, v___x_3949_);
v_i_3930_ = v___x_3950_;
v_b_3931_ = v___x_3948_;
goto _start;
}
else
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
v_a_3952_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3954_ = v___x_3947_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3947_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object* v_____s_3960_, lean_object* v_as_3961_, lean_object* v_sz_3962_, lean_object* v_i_3963_, lean_object* v_b_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
size_t v_sz_boxed_3976_; size_t v_i_boxed_3977_; lean_object* v_res_3978_; 
v_sz_boxed_3976_ = lean_unbox_usize(v_sz_3962_);
lean_dec(v_sz_3962_);
v_i_boxed_3977_ = lean_unbox_usize(v_i_3963_);
lean_dec(v_i_3963_);
v_res_3978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3960_, v_as_3961_, v_sz_boxed_3976_, v_i_boxed_3977_, v_b_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v_as_3961_);
lean_dec(v_____s_3960_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_3979_, lean_object* v_as_3980_, size_t v_sz_3981_, size_t v_i_3982_, lean_object* v_b_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
uint8_t v___x_3995_; 
v___x_3995_ = lean_usize_dec_lt(v_i_3982_, v_sz_3981_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3996_, 0, v_b_3983_);
return v___x_3996_;
}
else
{
lean_object* v_a_3997_; lean_object* v_p_3998_; lean_object* v___x_3999_; 
lean_dec_ref(v_b_3983_);
v_a_3997_ = lean_array_uget_borrowed(v_as_3980_, v_i_3982_);
v_p_3998_ = lean_ctor_get(v_a_3997_, 0);
v___x_3999_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_3998_, v_____s_3979_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v___x_4000_; size_t v___x_4001_; size_t v___x_4002_; lean_object* v___x_4003_; 
lean_dec_ref_known(v___x_3999_, 1);
v___x_4000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_4001_ = ((size_t)1ULL);
v___x_4002_ = lean_usize_add(v_i_3982_, v___x_4001_);
v___x_4003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3979_, v_as_3980_, v_sz_3981_, v___x_4002_, v___x_4000_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
return v___x_4003_;
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
v_a_4004_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3999_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3999_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object* v_____s_4012_, lean_object* v_as_4013_, lean_object* v_sz_4014_, lean_object* v_i_4015_, lean_object* v_b_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
size_t v_sz_boxed_4028_; size_t v_i_boxed_4029_; lean_object* v_res_4030_; 
v_sz_boxed_4028_ = lean_unbox_usize(v_sz_4014_);
lean_dec(v_sz_4014_);
v_i_boxed_4029_ = lean_unbox_usize(v_i_4015_);
lean_dec(v_i_4015_);
v_res_4030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4012_, v_as_4013_, v_sz_boxed_4028_, v_i_boxed_4029_, v_b_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v_as_4013_);
lean_dec(v_____s_4012_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_4034_, lean_object* v_as_4035_, size_t v_sz_4036_, size_t v_i_4037_, lean_object* v_b_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
uint8_t v___x_4050_; 
v___x_4050_ = lean_usize_dec_lt(v_i_4037_, v_sz_4036_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; 
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v_b_4038_);
return v___x_4051_;
}
else
{
lean_object* v_a_4052_; lean_object* v_p_4053_; lean_object* v___x_4054_; 
lean_dec_ref(v_b_4038_);
v_a_4052_ = lean_array_uget_borrowed(v_as_4035_, v_i_4037_);
v_p_4053_ = lean_ctor_get(v_a_4052_, 0);
v___x_4054_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4053_, v_____s_4034_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v___x_4055_; size_t v___x_4056_; size_t v___x_4057_; 
lean_dec_ref_known(v___x_4054_, 1);
v___x_4055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4056_ = ((size_t)1ULL);
v___x_4057_ = lean_usize_add(v_i_4037_, v___x_4056_);
v_i_4037_ = v___x_4057_;
v_b_4038_ = v___x_4055_;
goto _start;
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
v_a_4059_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4054_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4054_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_____s_4067_, lean_object* v_as_4068_, lean_object* v_sz_4069_, lean_object* v_i_4070_, lean_object* v_b_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
size_t v_sz_boxed_4083_; size_t v_i_boxed_4084_; lean_object* v_res_4085_; 
v_sz_boxed_4083_ = lean_unbox_usize(v_sz_4069_);
lean_dec(v_sz_4069_);
v_i_boxed_4084_ = lean_unbox_usize(v_i_4070_);
lean_dec(v_i_4070_);
v_res_4085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4067_, v_as_4068_, v_sz_boxed_4083_, v_i_boxed_4084_, v_b_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v_as_4068_);
lean_dec(v_____s_4067_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_4086_, lean_object* v_as_4087_, size_t v_sz_4088_, size_t v_i_4089_, lean_object* v_b_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
uint8_t v___x_4102_; 
v___x_4102_ = lean_usize_dec_lt(v_i_4089_, v_sz_4088_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4103_, 0, v_b_4090_);
return v___x_4103_;
}
else
{
lean_object* v_a_4104_; lean_object* v_p_4105_; lean_object* v___x_4106_; 
lean_dec_ref(v_b_4090_);
v_a_4104_ = lean_array_uget_borrowed(v_as_4087_, v_i_4089_);
v_p_4105_ = lean_ctor_get(v_a_4104_, 0);
v___x_4106_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4105_, v_____s_4086_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v___x_4107_; size_t v___x_4108_; size_t v___x_4109_; lean_object* v___x_4110_; 
lean_dec_ref_known(v___x_4106_, 1);
v___x_4107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4108_ = ((size_t)1ULL);
v___x_4109_ = lean_usize_add(v_i_4089_, v___x_4108_);
v___x_4110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4086_, v_as_4087_, v_sz_4088_, v___x_4109_, v___x_4107_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4110_;
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
v_a_4111_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4106_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4106_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_____s_4119_, lean_object* v_as_4120_, lean_object* v_sz_4121_, lean_object* v_i_4122_, lean_object* v_b_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
size_t v_sz_boxed_4135_; size_t v_i_boxed_4136_; lean_object* v_res_4137_; 
v_sz_boxed_4135_ = lean_unbox_usize(v_sz_4121_);
lean_dec(v_sz_4121_);
v_i_boxed_4136_ = lean_unbox_usize(v_i_4122_);
lean_dec(v_i_4122_);
v_res_4137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4119_, v_as_4120_, v_sz_boxed_4135_, v_i_boxed_4136_, v_b_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v_as_4120_);
lean_dec(v_____s_4119_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_init_4138_, lean_object* v_____s_4139_, lean_object* v_n_4140_, lean_object* v_b_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
if (lean_obj_tag(v_n_4140_) == 0)
{
lean_object* v_cs_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; size_t v_sz_4156_; size_t v___x_4157_; lean_object* v___x_4158_; 
v_cs_4153_ = lean_ctor_get(v_n_4140_, 0);
v___x_4154_ = lean_box(0);
v___x_4155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
lean_ctor_set(v___x_4155_, 1, v_b_4141_);
v_sz_4156_ = lean_array_size(v_cs_4153_);
v___x_4157_ = ((size_t)0ULL);
v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4138_, v_____s_4139_, v_cs_4153_, v_sz_4156_, v___x_4157_, v___x_4155_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4173_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4173_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4173_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v_fst_4163_; 
v_fst_4163_ = lean_ctor_get(v_a_4159_, 0);
if (lean_obj_tag(v_fst_4163_) == 0)
{
lean_object* v_snd_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v_snd_4164_ = lean_ctor_get(v_a_4159_, 1);
lean_inc(v_snd_4164_);
lean_dec(v_a_4159_);
v___x_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4165_, 0, v_snd_4164_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4165_);
v___x_4167_ = v___x_4161_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
else
{
lean_object* v_val_4169_; lean_object* v___x_4171_; 
lean_inc_ref(v_fst_4163_);
lean_dec(v_a_4159_);
v_val_4169_ = lean_ctor_get(v_fst_4163_, 0);
lean_inc(v_val_4169_);
lean_dec_ref_known(v_fst_4163_, 1);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v_val_4169_);
v___x_4171_ = v___x_4161_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_val_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
v_a_4174_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4158_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4158_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
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
lean_object* v_vs_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; size_t v_sz_4185_; size_t v___x_4186_; lean_object* v___x_4187_; 
v_vs_4182_ = lean_ctor_get(v_n_4140_, 0);
v___x_4183_ = lean_box(0);
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
lean_ctor_set(v___x_4184_, 1, v_b_4141_);
v_sz_4185_ = lean_array_size(v_vs_4182_);
v___x_4186_ = ((size_t)0ULL);
v___x_4187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4139_, v_vs_4182_, v_sz_4185_, v___x_4186_, v___x_4184_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4202_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4190_ = v___x_4187_;
v_isShared_4191_ = v_isSharedCheck_4202_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4187_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4202_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v_fst_4192_; 
v_fst_4192_ = lean_ctor_get(v_a_4188_, 0);
if (lean_obj_tag(v_fst_4192_) == 0)
{
lean_object* v_snd_4193_; lean_object* v___x_4194_; lean_object* v___x_4196_; 
v_snd_4193_ = lean_ctor_get(v_a_4188_, 1);
lean_inc(v_snd_4193_);
lean_dec(v_a_4188_);
v___x_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4194_, 0, v_snd_4193_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4194_);
v___x_4196_ = v___x_4190_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
else
{
lean_object* v_val_4198_; lean_object* v___x_4200_; 
lean_inc_ref(v_fst_4192_);
lean_dec(v_a_4188_);
v_val_4198_ = lean_ctor_get(v_fst_4192_, 0);
lean_inc(v_val_4198_);
lean_dec_ref_known(v_fst_4192_, 1);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v_val_4198_);
v___x_4200_ = v___x_4190_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_val_4198_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
v_a_4203_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4187_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4187_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_4211_, lean_object* v_____s_4212_, lean_object* v_as_4213_, size_t v_sz_4214_, size_t v_i_4215_, lean_object* v_b_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
uint8_t v___x_4228_; 
v___x_4228_ = lean_usize_dec_lt(v_i_4215_, v_sz_4214_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; 
v___x_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4229_, 0, v_b_4216_);
return v___x_4229_;
}
else
{
lean_object* v_snd_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4264_; 
v_snd_4230_ = lean_ctor_get(v_b_4216_, 1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_b_4216_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; 
v_unused_4265_ = lean_ctor_get(v_b_4216_, 0);
lean_dec(v_unused_4265_);
v___x_4232_ = v_b_4216_;
v_isShared_4233_ = v_isSharedCheck_4264_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_snd_4230_);
lean_dec(v_b_4216_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4264_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v_a_4234_; lean_object* v___x_4235_; 
v_a_4234_ = lean_array_uget_borrowed(v_as_4213_, v_i_4215_);
lean_inc(v_snd_4230_);
v___x_4235_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4211_, v_____s_4212_, v_a_4234_, v_snd_4230_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4255_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4238_ = v___x_4235_;
v_isShared_4239_ = v_isSharedCheck_4255_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4255_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
if (lean_obj_tag(v_a_4236_) == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4242_; 
v___x_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4240_, 0, v_a_4236_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4240_);
v___x_4242_ = v___x_4232_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4240_);
lean_ctor_set(v_reuseFailAlloc_4246_, 1, v_snd_4230_);
v___x_4242_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
lean_object* v___x_4244_; 
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v___x_4242_);
v___x_4244_ = v___x_4238_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4248_; lean_object* v___x_4250_; 
lean_del_object(v___x_4238_);
lean_dec(v_snd_4230_);
v_a_4247_ = lean_ctor_get(v_a_4236_, 0);
lean_inc(v_a_4247_);
lean_dec_ref_known(v_a_4236_, 1);
v___x_4248_ = lean_box(0);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 1, v_a_4247_);
lean_ctor_set(v___x_4232_, 0, v___x_4248_);
v___x_4250_ = v___x_4232_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_a_4247_);
v___x_4250_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
size_t v___x_4251_; size_t v___x_4252_; 
v___x_4251_ = ((size_t)1ULL);
v___x_4252_ = lean_usize_add(v_i_4215_, v___x_4251_);
v_i_4215_ = v___x_4252_;
v_b_4216_ = v___x_4250_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_del_object(v___x_4232_);
lean_dec(v_snd_4230_);
v_a_4256_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4235_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4235_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_4266_ = _args[0];
lean_object* v_____s_4267_ = _args[1];
lean_object* v_as_4268_ = _args[2];
lean_object* v_sz_4269_ = _args[3];
lean_object* v_i_4270_ = _args[4];
lean_object* v_b_4271_ = _args[5];
lean_object* v___y_4272_ = _args[6];
lean_object* v___y_4273_ = _args[7];
lean_object* v___y_4274_ = _args[8];
lean_object* v___y_4275_ = _args[9];
lean_object* v___y_4276_ = _args[10];
lean_object* v___y_4277_ = _args[11];
lean_object* v___y_4278_ = _args[12];
lean_object* v___y_4279_ = _args[13];
lean_object* v___y_4280_ = _args[14];
lean_object* v___y_4281_ = _args[15];
lean_object* v___y_4282_ = _args[16];
_start:
{
size_t v_sz_boxed_4283_; size_t v_i_boxed_4284_; lean_object* v_res_4285_; 
v_sz_boxed_4283_ = lean_unbox_usize(v_sz_4269_);
lean_dec(v_sz_4269_);
v_i_boxed_4284_ = lean_unbox_usize(v_i_4270_);
lean_dec(v_i_4270_);
v_res_4285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4266_, v_____s_4267_, v_as_4268_, v_sz_boxed_4283_, v_i_boxed_4284_, v_b_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v_as_4268_);
lean_dec(v_____s_4267_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_init_4286_, lean_object* v_____s_4287_, lean_object* v_n_4288_, lean_object* v_b_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4286_, v_____s_4287_, v_n_4288_, v_b_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v_n_4288_);
lean_dec(v_____s_4287_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(lean_object* v_____s_4302_, lean_object* v_t_4303_, lean_object* v_init_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v_root_4316_; lean_object* v_tail_4317_; lean_object* v___x_4318_; 
v_root_4316_ = lean_ctor_get(v_t_4303_, 0);
v_tail_4317_ = lean_ctor_get(v_t_4303_, 1);
v___x_4318_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4304_, v_____s_4302_, v_root_4316_, v_init_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4355_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4321_ = v___x_4318_;
v_isShared_4322_ = v_isSharedCheck_4355_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4318_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4355_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
if (lean_obj_tag(v_a_4319_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; 
v_a_4323_ = lean_ctor_get(v_a_4319_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v_a_4319_, 1);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 0, v_a_4323_);
v___x_4325_ = v___x_4321_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4323_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; size_t v_sz_4330_; size_t v___x_4331_; lean_object* v___x_4332_; 
lean_del_object(v___x_4321_);
v_a_4327_ = lean_ctor_get(v_a_4319_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v_a_4319_, 1);
v___x_4328_ = lean_box(0);
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
lean_ctor_set(v___x_4329_, 1, v_a_4327_);
v_sz_4330_ = lean_array_size(v_tail_4317_);
v___x_4331_ = ((size_t)0ULL);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4302_, v_tail_4317_, v_sz_4330_, v___x_4331_, v___x_4329_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4346_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4346_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4346_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v_fst_4337_; 
v_fst_4337_ = lean_ctor_get(v_a_4333_, 0);
if (lean_obj_tag(v_fst_4337_) == 0)
{
lean_object* v_snd_4338_; lean_object* v___x_4340_; 
v_snd_4338_ = lean_ctor_get(v_a_4333_, 1);
lean_inc(v_snd_4338_);
lean_dec(v_a_4333_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v_snd_4338_);
v___x_4340_ = v___x_4335_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_snd_4338_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
else
{
lean_object* v_val_4342_; lean_object* v___x_4344_; 
lean_inc_ref(v_fst_4337_);
lean_dec(v_a_4333_);
v_val_4342_ = lean_ctor_get(v_fst_4337_, 0);
lean_inc(v_val_4342_);
lean_dec_ref_known(v_fst_4337_, 1);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v_val_4342_);
v___x_4344_ = v___x_4335_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_val_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
v_a_4347_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4332_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4332_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
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
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v_a_4356_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4318_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4318_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_4364_, lean_object* v_t_4365_, lean_object* v_init_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_____s_4364_, v_t_4365_, v_init_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v_t_4365_);
lean_dec(v_____s_4364_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_4379_, size_t v_sz_4380_, size_t v_i_4381_, lean_object* v_b_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
uint8_t v___x_4394_; 
v___x_4394_ = lean_usize_dec_lt(v_i_4381_, v_sz_4380_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; 
v___x_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4395_, 0, v_b_4382_);
return v___x_4395_;
}
else
{
lean_object* v_snd_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4420_; 
v_snd_4396_ = lean_ctor_get(v_b_4382_, 1);
v_isSharedCheck_4420_ = !lean_is_exclusive(v_b_4382_);
if (v_isSharedCheck_4420_ == 0)
{
lean_object* v_unused_4421_; 
v_unused_4421_ = lean_ctor_get(v_b_4382_, 0);
lean_dec(v_unused_4421_);
v___x_4398_ = v_b_4382_;
v_isShared_4399_ = v_isSharedCheck_4420_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_snd_4396_);
lean_dec(v_b_4382_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4420_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v_a_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v_a_4400_ = lean_array_uget_borrowed(v_as_4379_, v_i_4381_);
v___x_4401_ = lean_box(0);
v___x_4402_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4396_, v_a_4400_, v___x_4401_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
lean_dec_ref_known(v___x_4402_, 1);
v___x_4403_ = lean_box(0);
v___x_4404_ = lean_unsigned_to_nat(1u);
v___x_4405_ = lean_nat_add(v_snd_4396_, v___x_4404_);
lean_dec(v_snd_4396_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 1, v___x_4405_);
lean_ctor_set(v___x_4398_, 0, v___x_4403_);
v___x_4407_ = v___x_4398_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
size_t v___x_4408_; size_t v___x_4409_; 
v___x_4408_ = ((size_t)1ULL);
v___x_4409_ = lean_usize_add(v_i_4381_, v___x_4408_);
v_i_4381_ = v___x_4409_;
v_b_4382_ = v___x_4407_;
goto _start;
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_del_object(v___x_4398_);
lean_dec(v_snd_4396_);
v_a_4412_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4402_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4402_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_4422_, lean_object* v_sz_4423_, lean_object* v_i_4424_, lean_object* v_b_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
size_t v_sz_boxed_4437_; size_t v_i_boxed_4438_; lean_object* v_res_4439_; 
v_sz_boxed_4437_ = lean_unbox_usize(v_sz_4423_);
lean_dec(v_sz_4423_);
v_i_boxed_4438_ = lean_unbox_usize(v_i_4424_);
lean_dec(v_i_4424_);
v_res_4439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4422_, v_sz_boxed_4437_, v_i_boxed_4438_, v_b_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v_as_4422_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_4440_, size_t v_sz_4441_, size_t v_i_4442_, lean_object* v_b_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
uint8_t v___x_4455_; 
v___x_4455_ = lean_usize_dec_lt(v_i_4442_, v_sz_4441_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4456_, 0, v_b_4443_);
return v___x_4456_;
}
else
{
lean_object* v_snd_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4481_; 
v_snd_4457_ = lean_ctor_get(v_b_4443_, 1);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_b_4443_);
if (v_isSharedCheck_4481_ == 0)
{
lean_object* v_unused_4482_; 
v_unused_4482_ = lean_ctor_get(v_b_4443_, 0);
lean_dec(v_unused_4482_);
v___x_4459_ = v_b_4443_;
v_isShared_4460_ = v_isSharedCheck_4481_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_snd_4457_);
lean_dec(v_b_4443_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4481_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_a_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v_a_4461_ = lean_array_uget_borrowed(v_as_4440_, v_i_4442_);
v___x_4462_ = lean_box(0);
v___x_4463_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4457_, v_a_4461_, v___x_4462_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4468_; 
lean_dec_ref_known(v___x_4463_, 1);
v___x_4464_ = lean_box(0);
v___x_4465_ = lean_unsigned_to_nat(1u);
v___x_4466_ = lean_nat_add(v_snd_4457_, v___x_4465_);
lean_dec(v_snd_4457_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 1, v___x_4466_);
lean_ctor_set(v___x_4459_, 0, v___x_4464_);
v___x_4468_ = v___x_4459_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
size_t v___x_4469_; size_t v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = ((size_t)1ULL);
v___x_4470_ = lean_usize_add(v_i_4442_, v___x_4469_);
v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4440_, v_sz_4441_, v___x_4470_, v___x_4468_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
return v___x_4471_;
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_del_object(v___x_4459_);
lean_dec(v_snd_4457_);
v_a_4473_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4463_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4463_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_4483_, lean_object* v_sz_4484_, lean_object* v_i_4485_, lean_object* v_b_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
size_t v_sz_boxed_4498_; size_t v_i_boxed_4499_; lean_object* v_res_4500_; 
v_sz_boxed_4498_ = lean_unbox_usize(v_sz_4484_);
lean_dec(v_sz_4484_);
v_i_boxed_4499_ = lean_unbox_usize(v_i_4485_);
lean_dec(v_i_4485_);
v_res_4500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_4483_, v_sz_boxed_4498_, v_i_boxed_4499_, v_b_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v_as_4483_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_init_4501_, lean_object* v_n_4502_, lean_object* v_b_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
if (lean_obj_tag(v_n_4502_) == 0)
{
lean_object* v_cs_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; size_t v_sz_4518_; size_t v___x_4519_; lean_object* v___x_4520_; 
v_cs_4515_ = lean_ctor_get(v_n_4502_, 0);
v___x_4516_ = lean_box(0);
v___x_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
lean_ctor_set(v___x_4517_, 1, v_b_4503_);
v_sz_4518_ = lean_array_size(v_cs_4515_);
v___x_4519_ = ((size_t)0ULL);
v___x_4520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4501_, v_cs_4515_, v_sz_4518_, v___x_4519_, v___x_4517_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4535_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4523_ = v___x_4520_;
v_isShared_4524_ = v_isSharedCheck_4535_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4520_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4535_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_fst_4525_; 
v_fst_4525_ = lean_ctor_get(v_a_4521_, 0);
if (lean_obj_tag(v_fst_4525_) == 0)
{
lean_object* v_snd_4526_; lean_object* v___x_4527_; lean_object* v___x_4529_; 
v_snd_4526_ = lean_ctor_get(v_a_4521_, 1);
lean_inc(v_snd_4526_);
lean_dec(v_a_4521_);
v___x_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4527_, 0, v_snd_4526_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4527_);
v___x_4529_ = v___x_4523_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4527_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
else
{
lean_object* v_val_4531_; lean_object* v___x_4533_; 
lean_inc_ref(v_fst_4525_);
lean_dec(v_a_4521_);
v_val_4531_ = lean_ctor_get(v_fst_4525_, 0);
lean_inc(v_val_4531_);
lean_dec_ref_known(v_fst_4525_, 1);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v_val_4531_);
v___x_4533_ = v___x_4523_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_val_4531_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
v_a_4536_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4520_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4520_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
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
lean_object* v_vs_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; size_t v_sz_4547_; size_t v___x_4548_; lean_object* v___x_4549_; 
v_vs_4544_ = lean_ctor_get(v_n_4502_, 0);
v___x_4545_ = lean_box(0);
v___x_4546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
lean_ctor_set(v___x_4546_, 1, v_b_4503_);
v_sz_4547_ = lean_array_size(v_vs_4544_);
v___x_4548_ = ((size_t)0ULL);
v___x_4549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_4544_, v_sz_4547_, v___x_4548_, v___x_4546_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4564_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4552_ = v___x_4549_;
v_isShared_4553_ = v_isSharedCheck_4564_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4549_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4564_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v_fst_4554_; 
v_fst_4554_ = lean_ctor_get(v_a_4550_, 0);
if (lean_obj_tag(v_fst_4554_) == 0)
{
lean_object* v_snd_4555_; lean_object* v___x_4556_; lean_object* v___x_4558_; 
v_snd_4555_ = lean_ctor_get(v_a_4550_, 1);
lean_inc(v_snd_4555_);
lean_dec(v_a_4550_);
v___x_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4556_, 0, v_snd_4555_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4556_);
v___x_4558_ = v___x_4552_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
else
{
lean_object* v_val_4560_; lean_object* v___x_4562_; 
lean_inc_ref(v_fst_4554_);
lean_dec(v_a_4550_);
v_val_4560_ = lean_ctor_get(v_fst_4554_, 0);
lean_inc(v_val_4560_);
lean_dec_ref_known(v_fst_4554_, 1);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v_val_4560_);
v___x_4562_ = v___x_4552_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_val_4560_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
else
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
v_a_4565_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4549_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4549_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_init_4573_, lean_object* v_as_4574_, size_t v_sz_4575_, size_t v_i_4576_, lean_object* v_b_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
uint8_t v___x_4589_; 
v___x_4589_ = lean_usize_dec_lt(v_i_4576_, v_sz_4575_);
if (v___x_4589_ == 0)
{
lean_object* v___x_4590_; 
v___x_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4590_, 0, v_b_4577_);
return v___x_4590_;
}
else
{
lean_object* v_snd_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4625_; 
v_snd_4591_ = lean_ctor_get(v_b_4577_, 1);
v_isSharedCheck_4625_ = !lean_is_exclusive(v_b_4577_);
if (v_isSharedCheck_4625_ == 0)
{
lean_object* v_unused_4626_; 
v_unused_4626_ = lean_ctor_get(v_b_4577_, 0);
lean_dec(v_unused_4626_);
v___x_4593_ = v_b_4577_;
v_isShared_4594_ = v_isSharedCheck_4625_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_snd_4591_);
lean_dec(v_b_4577_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4625_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v_a_4595_; lean_object* v___x_4596_; 
v_a_4595_ = lean_array_uget_borrowed(v_as_4574_, v_i_4576_);
lean_inc(v_snd_4591_);
v___x_4596_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4573_, v_a_4595_, v_snd_4591_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4616_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4599_ = v___x_4596_;
v_isShared_4600_ = v_isSharedCheck_4616_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4596_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4616_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
if (lean_obj_tag(v_a_4597_) == 0)
{
lean_object* v___x_4601_; lean_object* v___x_4603_; 
v___x_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4601_, 0, v_a_4597_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4601_);
v___x_4603_ = v___x_4593_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_snd_4591_);
v___x_4603_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
lean_object* v___x_4605_; 
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 0, v___x_4603_);
v___x_4605_ = v___x_4599_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
lean_del_object(v___x_4599_);
lean_dec(v_snd_4591_);
v_a_4608_ = lean_ctor_get(v_a_4597_, 0);
lean_inc(v_a_4608_);
lean_dec_ref_known(v_a_4597_, 1);
v___x_4609_ = lean_box(0);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 1, v_a_4608_);
lean_ctor_set(v___x_4593_, 0, v___x_4609_);
v___x_4611_ = v___x_4593_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4615_, 1, v_a_4608_);
v___x_4611_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
size_t v___x_4612_; size_t v___x_4613_; 
v___x_4612_ = ((size_t)1ULL);
v___x_4613_ = lean_usize_add(v_i_4576_, v___x_4612_);
v_i_4576_ = v___x_4613_;
v_b_4577_ = v___x_4611_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_del_object(v___x_4593_);
lean_dec(v_snd_4591_);
v_a_4617_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4596_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4596_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object* v_init_4627_, lean_object* v_as_4628_, lean_object* v_sz_4629_, lean_object* v_i_4630_, lean_object* v_b_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
size_t v_sz_boxed_4643_; size_t v_i_boxed_4644_; lean_object* v_res_4645_; 
v_sz_boxed_4643_ = lean_unbox_usize(v_sz_4629_);
lean_dec(v_sz_4629_);
v_i_boxed_4644_ = lean_unbox_usize(v_i_4630_);
lean_dec(v_i_4630_);
v_res_4645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4627_, v_as_4628_, v_sz_boxed_4643_, v_i_boxed_4644_, v_b_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v_as_4628_);
lean_dec(v_init_4627_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_init_4646_, lean_object* v_n_4647_, lean_object* v_b_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
lean_object* v_res_4660_; 
v_res_4660_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4646_, v_n_4647_, v_b_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v_n_4647_);
lean_dec(v_init_4646_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_4661_, size_t v_sz_4662_, size_t v_i_4663_, lean_object* v_b_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
uint8_t v___x_4676_; 
v___x_4676_ = lean_usize_dec_lt(v_i_4663_, v_sz_4662_);
if (v___x_4676_ == 0)
{
lean_object* v___x_4677_; 
v___x_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4677_, 0, v_b_4664_);
return v___x_4677_;
}
else
{
lean_object* v_snd_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4702_; 
v_snd_4678_ = lean_ctor_get(v_b_4664_, 1);
v_isSharedCheck_4702_ = !lean_is_exclusive(v_b_4664_);
if (v_isSharedCheck_4702_ == 0)
{
lean_object* v_unused_4703_; 
v_unused_4703_ = lean_ctor_get(v_b_4664_, 0);
lean_dec(v_unused_4703_);
v___x_4680_ = v_b_4664_;
v_isShared_4681_ = v_isSharedCheck_4702_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_snd_4678_);
lean_dec(v_b_4664_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4702_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v_a_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v_a_4682_ = lean_array_uget_borrowed(v_as_4661_, v_i_4663_);
v___x_4683_ = lean_box(0);
v___x_4684_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4678_, v_a_4682_, v___x_4683_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
lean_dec_ref_known(v___x_4684_, 1);
v___x_4685_ = lean_box(0);
v___x_4686_ = lean_unsigned_to_nat(1u);
v___x_4687_ = lean_nat_add(v_snd_4678_, v___x_4686_);
lean_dec(v_snd_4678_);
if (v_isShared_4681_ == 0)
{
lean_ctor_set(v___x_4680_, 1, v___x_4687_);
lean_ctor_set(v___x_4680_, 0, v___x_4685_);
v___x_4689_ = v___x_4680_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v___x_4687_);
v___x_4689_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
size_t v___x_4690_; size_t v___x_4691_; 
v___x_4690_ = ((size_t)1ULL);
v___x_4691_ = lean_usize_add(v_i_4663_, v___x_4690_);
v_i_4663_ = v___x_4691_;
v_b_4664_ = v___x_4689_;
goto _start;
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_del_object(v___x_4680_);
lean_dec(v_snd_4678_);
v_a_4694_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4684_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4684_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_4704_, lean_object* v_sz_4705_, lean_object* v_i_4706_, lean_object* v_b_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
size_t v_sz_boxed_4719_; size_t v_i_boxed_4720_; lean_object* v_res_4721_; 
v_sz_boxed_4719_ = lean_unbox_usize(v_sz_4705_);
lean_dec(v_sz_4705_);
v_i_boxed_4720_ = lean_unbox_usize(v_i_4706_);
lean_dec(v_i_4706_);
v_res_4721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4704_, v_sz_boxed_4719_, v_i_boxed_4720_, v_b_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v_as_4704_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_4722_, size_t v_sz_4723_, size_t v_i_4724_, lean_object* v_b_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
uint8_t v___x_4737_; 
v___x_4737_ = lean_usize_dec_lt(v_i_4724_, v_sz_4723_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; 
v___x_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4738_, 0, v_b_4725_);
return v___x_4738_;
}
else
{
lean_object* v_snd_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4763_; 
v_snd_4739_ = lean_ctor_get(v_b_4725_, 1);
v_isSharedCheck_4763_ = !lean_is_exclusive(v_b_4725_);
if (v_isSharedCheck_4763_ == 0)
{
lean_object* v_unused_4764_; 
v_unused_4764_ = lean_ctor_get(v_b_4725_, 0);
lean_dec(v_unused_4764_);
v___x_4741_ = v_b_4725_;
v_isShared_4742_ = v_isSharedCheck_4763_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_snd_4739_);
lean_dec(v_b_4725_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4763_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v_a_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v_a_4743_ = lean_array_uget_borrowed(v_as_4722_, v_i_4724_);
v___x_4744_ = lean_box(0);
v___x_4745_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4739_, v_a_4743_, v___x_4744_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4750_; 
lean_dec_ref_known(v___x_4745_, 1);
v___x_4746_ = lean_box(0);
v___x_4747_ = lean_unsigned_to_nat(1u);
v___x_4748_ = lean_nat_add(v_snd_4739_, v___x_4747_);
lean_dec(v_snd_4739_);
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 1, v___x_4748_);
lean_ctor_set(v___x_4741_, 0, v___x_4746_);
v___x_4750_ = v___x_4741_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v___x_4748_);
v___x_4750_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
size_t v___x_4751_; size_t v___x_4752_; lean_object* v___x_4753_; 
v___x_4751_ = ((size_t)1ULL);
v___x_4752_ = lean_usize_add(v_i_4724_, v___x_4751_);
v___x_4753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4722_, v_sz_4723_, v___x_4752_, v___x_4750_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_);
return v___x_4753_;
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_del_object(v___x_4741_);
lean_dec(v_snd_4739_);
v_a_4755_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4745_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4745_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_4765_, lean_object* v_sz_4766_, lean_object* v_i_4767_, lean_object* v_b_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
size_t v_sz_boxed_4780_; size_t v_i_boxed_4781_; lean_object* v_res_4782_; 
v_sz_boxed_4780_ = lean_unbox_usize(v_sz_4766_);
lean_dec(v_sz_4766_);
v_i_boxed_4781_ = lean_unbox_usize(v_i_4767_);
lean_dec(v_i_4767_);
v_res_4782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_as_4765_, v_sz_boxed_4780_, v_i_boxed_4781_, v_b_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec(v___y_4769_);
lean_dec_ref(v_as_4765_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(lean_object* v_t_4783_, lean_object* v_init_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_){
_start:
{
lean_object* v_root_4796_; lean_object* v_tail_4797_; lean_object* v___x_4798_; 
v_root_4796_ = lean_ctor_get(v_t_4783_, 0);
v_tail_4797_ = lean_ctor_get(v_t_4783_, 1);
lean_inc(v_init_4784_);
v___x_4798_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4784_, v_root_4796_, v_init_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
lean_dec(v_init_4784_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4835_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4801_ = v___x_4798_;
v_isShared_4802_ = v_isSharedCheck_4835_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4798_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4835_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
if (lean_obj_tag(v_a_4799_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4805_; 
v_a_4803_ = lean_ctor_get(v_a_4799_, 0);
lean_inc(v_a_4803_);
lean_dec_ref_known(v_a_4799_, 1);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v_a_4803_);
v___x_4805_ = v___x_4801_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4803_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; size_t v_sz_4810_; size_t v___x_4811_; lean_object* v___x_4812_; 
lean_del_object(v___x_4801_);
v_a_4807_ = lean_ctor_get(v_a_4799_, 0);
lean_inc(v_a_4807_);
lean_dec_ref_known(v_a_4799_, 1);
v___x_4808_ = lean_box(0);
v___x_4809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4808_);
lean_ctor_set(v___x_4809_, 1, v_a_4807_);
v_sz_4810_ = lean_array_size(v_tail_4797_);
v___x_4811_ = ((size_t)0ULL);
v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_tail_4797_, v_sz_4810_, v___x_4811_, v___x_4809_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4826_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4815_ = v___x_4812_;
v_isShared_4816_ = v_isSharedCheck_4826_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4812_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4826_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v_fst_4817_; 
v_fst_4817_ = lean_ctor_get(v_a_4813_, 0);
if (lean_obj_tag(v_fst_4817_) == 0)
{
lean_object* v_snd_4818_; lean_object* v___x_4820_; 
v_snd_4818_ = lean_ctor_get(v_a_4813_, 1);
lean_inc(v_snd_4818_);
lean_dec(v_a_4813_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v_snd_4818_);
v___x_4820_ = v___x_4815_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_snd_4818_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
else
{
lean_object* v_val_4822_; lean_object* v___x_4824_; 
lean_inc_ref(v_fst_4817_);
lean_dec(v_a_4813_);
v_val_4822_ = lean_ctor_get(v_fst_4817_, 0);
lean_inc(v_val_4822_);
lean_dec_ref_known(v_fst_4817_, 1);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v_val_4822_);
v___x_4824_ = v___x_4815_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_val_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
v_a_4827_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4812_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4812_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
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
}
}
else
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4843_; 
v_a_4836_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4838_ = v___x_4798_;
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4798_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4841_; 
if (v_isShared_4839_ == 0)
{
v___x_4841_ = v___x_4838_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v_a_4836_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_4844_, lean_object* v_init_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_t_4844_, v_init_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v_t_4844_);
return v_res_4857_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4860_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1));
v___x_4861_ = lean_unsigned_to_nat(2u);
v___x_4862_ = lean_unsigned_to_nat(103u);
v___x_4863_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0));
v___x_4864_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_4865_ = l_mkPanicMessageWithDecl(v___x_4864_, v___x_4863_, v___x_4862_, v___x_4861_, v___x_4860_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4866_, v_a_4874_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v_vars_4879_; lean_object* v_diseqs_4880_; lean_object* v_size_4881_; lean_object* v_size_4882_; uint8_t v___x_4883_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v_vars_4879_ = lean_ctor_get(v_a_4878_, 0);
lean_inc_ref(v_vars_4879_);
v_diseqs_4880_ = lean_ctor_get(v_a_4878_, 9);
lean_inc_ref(v_diseqs_4880_);
lean_dec(v_a_4878_);
v_size_4881_ = lean_ctor_get(v_vars_4879_, 2);
lean_inc(v_size_4881_);
lean_dec_ref(v_vars_4879_);
v_size_4882_ = lean_ctor_get(v_diseqs_4880_, 2);
v___x_4883_ = lean_nat_dec_eq(v_size_4881_, v_size_4882_);
lean_dec(v_size_4881_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
lean_dec_ref(v_diseqs_4880_);
v___x_4884_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2);
v___x_4885_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_4884_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
return v___x_4885_;
}
else
{
lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4886_ = lean_unsigned_to_nat(0u);
v___x_4887_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_diseqs_4880_, v___x_4886_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
lean_dec_ref(v_diseqs_4880_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4895_; 
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4895_ == 0)
{
lean_object* v_unused_4896_; 
v_unused_4896_ = lean_ctor_get(v___x_4887_, 0);
lean_dec(v_unused_4896_);
v___x_4889_ = v___x_4887_;
v_isShared_4890_ = v_isSharedCheck_4895_;
goto v_resetjp_4888_;
}
else
{
lean_dec(v___x_4887_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4895_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4891_; lean_object* v___x_4893_; 
v___x_4891_ = lean_box(0);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4891_);
v___x_4893_ = v___x_4889_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
v_a_4897_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4887_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4887_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
v_a_4905_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4877_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4877_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___boxed(lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_);
lean_dec(v_a_4922_);
lean_dec_ref(v_a_4921_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
lean_dec(v_a_4916_);
lean_dec_ref(v_a_4915_);
lean_dec(v_a_4914_);
lean_dec(v_a_4913_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v___x_4937_; 
lean_dec_ref_known(v___x_4936_, 1);
v___x_4937_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v___x_4938_; 
lean_dec_ref_known(v___x_4937_, 1);
v___x_4938_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v___x_4939_; 
lean_dec_ref_known(v___x_4938_, 1);
v___x_4939_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v___x_4940_; 
lean_dec_ref_known(v___x_4939_, 1);
v___x_4940_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v___x_4941_; 
lean_dec_ref_known(v___x_4940_, 1);
v___x_4941_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v___x_4942_; 
lean_dec_ref_known(v___x_4941_, 1);
v___x_4942_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
return v___x_4942_;
}
else
{
return v___x_4941_;
}
}
else
{
return v___x_4940_;
}
}
else
{
return v___x_4939_;
}
}
else
{
return v___x_4938_;
}
}
else
{
return v___x_4937_;
}
}
else
{
return v___x_4936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec_ref(v_a_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec(v_a_4944_);
lean_dec(v_a_4943_);
return v_res_4954_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
