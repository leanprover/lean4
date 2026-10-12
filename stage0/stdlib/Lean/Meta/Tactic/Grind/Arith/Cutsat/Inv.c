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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
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
uint8_t l_Int_Internal_Linear_Poly_checkCoeffs(lean_object* v_x_3_){
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
LEAN_EXPORT void l_Int_Internal_Linear_Poly_checkCoeffs_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3_ = stack[0].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_x_3_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCoeffs___boxed(lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_x_12_);
lean_dec_ref(v_x_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_15_;
}
}
lean_object* l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(lean_object* v_msg_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_1290__overap_29_; lean_object* v___x_30_; 
v___x_28_ = lean_obj_once(&l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_1290__overap_29_ = lean_panic_fn_borrowed(v___x_28_, v_msg_16_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
lean_inc(v___y_24_);
lean_inc_ref(v___y_23_);
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
lean_inc(v___y_20_);
lean_inc_ref(v___y_19_);
lean_inc(v___y_18_);
lean_inc(v___y_17_);
v___x_30_ = lean_apply_11(v___x_1290__overap_29_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, lean_box(0));
return v___x_30_;
}
}
LEAN_EXPORT void l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_16_ = stack[0].m_obj;
lean_object* v___y_17_ = stack[1].m_obj;
lean_object* v___y_18_ = stack[2].m_obj;
lean_object* v___y_19_ = stack[3].m_obj;
lean_object* v___y_20_ = stack[4].m_obj;
lean_object* v___y_21_ = stack[5].m_obj;
lean_object* v___y_22_ = stack[6].m_obj;
lean_object* v___y_23_ = stack[7].m_obj;
lean_object* v___y_24_ = stack[8].m_obj;
lean_object* v___y_25_ = stack[9].m_obj;
lean_object* v___y_26_ = stack[10].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v_msg_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___boxed(lean_object* v_msg_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v_msg_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec(v___y_33_);
return v_res_44_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_48_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__2));
v___x_49_ = lean_unsigned_to_nat(2u);
v___x_50_ = lean_unsigned_to_nat(23u);
v___x_51_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__1));
v___x_52_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_53_ = l_mkPanicMessageWithDecl(v___x_52_, v___x_51_, v___x_50_, v___x_49_, v___x_48_);
return v___x_53_;
}
}
lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars(lean_object* v_p_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
if (lean_obj_tag(v_p_54_) == 1)
{
lean_object* v_v_66_; lean_object* v_p_67_; lean_object* v___x_68_; 
v_v_66_ = lean_ctor_get(v_p_54_, 1);
v_p_67_ = lean_ctor_get(v_p_54_, 2);
v___x_68_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_v_66_, v_a_55_, v_a_63_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; uint8_t v___x_70_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
lean_dec_ref_known(v___x_68_, 1);
v___x_70_ = lean_unbox(v_a_69_);
lean_dec(v_a_69_);
if (v___x_70_ == 0)
{
v_p_54_ = v_p_67_;
goto _start;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3, &l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3_once, _init_l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3);
v___x_73_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_72_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
return v___x_73_;
}
}
else
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
v_a_74_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_68_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_68_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_checkNoElimVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_54_ = stack[0].m_obj;
lean_object* v_a_55_ = stack[1].m_obj;
lean_object* v_a_56_ = stack[2].m_obj;
lean_object* v_a_57_ = stack[3].m_obj;
lean_object* v_a_58_ = stack[4].m_obj;
lean_object* v_a_59_ = stack[5].m_obj;
lean_object* v_a_60_ = stack[6].m_obj;
lean_object* v_a_61_ = stack[7].m_obj;
lean_object* v_a_62_ = stack[8].m_obj;
lean_object* v_a_63_ = stack[9].m_obj;
lean_object* v_a_64_ = stack[10].m_obj;
lean_object* v_res_84_;
v_res_84_ = l_Int_Internal_Linear_Poly_checkNoElimVars(v_p_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars___boxed(lean_object* v_p_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Int_Internal_Linear_Poly_checkNoElimVars(v_p_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_p_85_);
return v_res_97_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(lean_object* v_k_98_, lean_object* v_t_99_){
_start:
{
if (lean_obj_tag(v_t_99_) == 0)
{
lean_object* v_k_100_; lean_object* v_l_101_; lean_object* v_r_102_; uint8_t v___x_103_; 
v_k_100_ = lean_ctor_get(v_t_99_, 1);
v_l_101_ = lean_ctor_get(v_t_99_, 3);
v_r_102_ = lean_ctor_get(v_t_99_, 4);
v___x_103_ = lean_nat_dec_lt(v_k_98_, v_k_100_);
if (v___x_103_ == 0)
{
uint8_t v___x_104_; 
v___x_104_ = lean_nat_dec_eq(v_k_98_, v_k_100_);
if (v___x_104_ == 0)
{
v_t_99_ = v_r_102_;
goto _start;
}
else
{
return v___x_104_;
}
}
else
{
v_t_99_ = v_l_101_;
goto _start;
}
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_98_ = stack[0].m_obj;
lean_object* v_t_99_ = stack[1].m_obj;
uint8_t v_res_108_;
v_res_108_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_98_, v_t_99_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg___boxed(lean_object* v_k_109_, lean_object* v_t_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_109_, v_t_110_);
lean_dec(v_t_110_);
lean_dec(v_k_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__1));
v___x_116_ = lean_unsigned_to_nat(4u);
v___x_117_ = lean_unsigned_to_nat(30u);
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__0));
v___x_119_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_120_ = l_mkPanicMessageWithDecl(v___x_119_, v___x_118_, v___x_117_, v___x_116_, v___x_115_);
return v___x_120_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(lean_object* v_y_121_, lean_object* v_p_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
if (lean_obj_tag(v_p_122_) == 1)
{
lean_object* v_v_134_; lean_object* v_p_135_; lean_object* v___x_136_; 
v_v_134_ = lean_ctor_get(v_p_122_, 1);
v_p_135_ = lean_ctor_get(v_p_122_, 2);
v___x_136_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_v_134_, v_a_123_, v_a_131_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; uint8_t v___x_138_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
v___x_138_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_y_121_, v_a_137_);
lean_dec(v_a_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2);
v___x_140_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_139_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
return v___x_140_;
}
else
{
v_p_122_ = v_p_135_;
goto _start;
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_136_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_136_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_121_ = stack[0].m_obj;
lean_object* v_p_122_ = stack[1].m_obj;
lean_object* v_a_123_ = stack[2].m_obj;
lean_object* v_a_124_ = stack[3].m_obj;
lean_object* v_a_125_ = stack[4].m_obj;
lean_object* v_a_126_ = stack[5].m_obj;
lean_object* v_a_127_ = stack[6].m_obj;
lean_object* v_a_128_ = stack[7].m_obj;
lean_object* v_a_129_ = stack[8].m_obj;
lean_object* v_a_130_ = stack[9].m_obj;
lean_object* v_a_131_ = stack[10].m_obj;
lean_object* v_a_132_ = stack[11].m_obj;
lean_object* v_res_152_;
v_res_152_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(v_y_121_, v_p_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___boxed(lean_object* v_y_153_, lean_object* v_p_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(v_y_153_, v_p_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_p_154_);
lean_dec(v_y_153_);
return v_res_166_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0(lean_object* v_00_u03b2_167_, lean_object* v_k_168_, lean_object* v_t_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_168_, v_t_169_);
return v___x_170_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_168_ = stack[1].m_obj;
lean_object* v_t_169_ = stack[2].m_obj;
uint8_t v_res_171_;
v_res_171_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0(lean_box(0), v_k_168_, v_t_169_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___boxed(lean_object* v_00_u03b2_172_, lean_object* v_k_173_, lean_object* v_t_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0(v_00_u03b2_172_, v_k_173_, v_t_174_);
lean_dec(v_t_174_);
lean_dec(v_k_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
lean_object* l_Int_Internal_Linear_Poly_checkOccs(lean_object* v_p_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
if (lean_obj_tag(v_p_177_) == 1)
{
lean_object* v_v_189_; lean_object* v_p_190_; lean_object* v___x_191_; 
v_v_189_ = lean_ctor_get(v_p_177_, 1);
v_p_190_ = lean_ctor_get(v_p_177_, 2);
v___x_191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(v_v_189_, v_p_190_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_box(0);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_checkOccs_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_177_ = stack[0].m_obj;
lean_object* v_a_178_ = stack[1].m_obj;
lean_object* v_a_179_ = stack[2].m_obj;
lean_object* v_a_180_ = stack[3].m_obj;
lean_object* v_a_181_ = stack[4].m_obj;
lean_object* v_a_182_ = stack[5].m_obj;
lean_object* v_a_183_ = stack[6].m_obj;
lean_object* v_a_184_ = stack[7].m_obj;
lean_object* v_a_185_ = stack[8].m_obj;
lean_object* v_a_186_ = stack[9].m_obj;
lean_object* v_a_187_ = stack[10].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Int_Internal_Linear_Poly_checkOccs(v_p_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkOccs___boxed(lean_object* v_p_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Int_Internal_Linear_Poly_checkOccs(v_p_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_p_195_);
return v_res_207_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__1));
v___x_211_ = lean_unsigned_to_nat(2u);
v___x_212_ = lean_unsigned_to_nat(41u);
v___x_213_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_214_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_215_ = l_mkPanicMessageWithDecl(v___x_214_, v___x_213_, v___x_212_, v___x_211_, v___x_210_);
return v___x_215_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_218_ = lean_unsigned_to_nat(24u);
v___x_219_ = lean_unsigned_to_nat(40u);
v___x_220_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_221_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_222_ = l_mkPanicMessageWithDecl(v___x_221_, v___x_220_, v___x_219_, v___x_218_, v___x_217_);
return v___x_222_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__5));
v___x_225_ = lean_unsigned_to_nat(2u);
v___x_226_ = lean_unsigned_to_nat(35u);
v___x_227_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_228_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_229_ = l_mkPanicMessageWithDecl(v___x_228_, v___x_227_, v___x_226_, v___x_225_, v___x_224_);
return v___x_229_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_231_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__7));
v___x_232_ = lean_unsigned_to_nat(2u);
v___x_233_ = lean_unsigned_to_nat(36u);
v___x_234_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_235_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_236_ = l_mkPanicMessageWithDecl(v___x_235_, v___x_234_, v___x_233_, v___x_232_, v___x_231_);
return v___x_236_;
}
}
lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf(lean_object* v_p_237_, lean_object* v_x_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; uint8_t v___x_269_; 
v___x_269_ = l_Int_Internal_Linear_Poly_isSorted(v_p_237_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6);
v___x_271_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_270_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
return v___x_271_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_237_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8);
v___x_274_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_273_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_239_, v_a_247_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; uint8_t v___x_277_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = lean_unbox(v_a_276_);
lean_dec(v_a_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = l_Int_Internal_Linear_Poly_checkNoElimVars(v_p_237_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; 
lean_dec_ref_known(v___x_278_, 1);
v___x_279_ = l_Int_Internal_Linear_Poly_checkOccs(v_p_237_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_dec_ref_known(v___x_279_, 1);
v___y_251_ = v_a_239_;
v___y_252_ = v_a_240_;
v___y_253_ = v_a_241_;
v___y_254_ = v_a_242_;
v___y_255_ = v_a_243_;
v___y_256_ = v_a_244_;
v___y_257_ = v_a_245_;
v___y_258_ = v_a_246_;
v___y_259_ = v_a_247_;
v___y_260_ = v_a_248_;
goto v___jp_250_;
}
else
{
return v___x_279_;
}
}
else
{
return v___x_278_;
}
}
else
{
v___y_251_ = v_a_239_;
v___y_252_ = v_a_240_;
v___y_253_ = v_a_241_;
v___y_254_ = v_a_242_;
v___y_255_ = v_a_243_;
v___y_256_ = v_a_244_;
v___y_257_ = v_a_245_;
v___y_258_ = v_a_246_;
v___y_259_ = v_a_247_;
v___y_260_ = v_a_248_;
goto v___jp_250_;
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_a_280_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_275_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_275_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
v___jp_250_:
{
if (lean_obj_tag(v_p_237_) == 1)
{
lean_object* v_v_261_; uint8_t v___x_262_; 
v_v_261_ = lean_ctor_get(v_p_237_, 1);
v___x_262_ = lean_nat_dec_eq(v_x_238_, v_v_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2);
v___x_264_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_263_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_box(0);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4);
v___x_268_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_267_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_checkCnstrOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_237_ = stack[0].m_obj;
lean_object* v_x_238_ = stack[1].m_obj;
lean_object* v_a_239_ = stack[2].m_obj;
lean_object* v_a_240_ = stack[3].m_obj;
lean_object* v_a_241_ = stack[4].m_obj;
lean_object* v_a_242_ = stack[5].m_obj;
lean_object* v_a_243_ = stack[6].m_obj;
lean_object* v_a_244_ = stack[7].m_obj;
lean_object* v_a_245_ = stack[8].m_obj;
lean_object* v_a_246_ = stack[9].m_obj;
lean_object* v_a_247_ = stack[10].m_obj;
lean_object* v_a_248_ = stack[11].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_237_, v_x_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___boxed(lean_object* v_p_289_, lean_object* v_x_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_289_, v_x_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec(v_a_291_);
lean_dec(v_x_290_);
lean_dec_ref(v_p_289_);
return v_res_302_;
}
}
lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_3860__overap_316_; lean_object* v___x_317_; 
v___x_315_ = lean_obj_once(&l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_3860__overap_316_ = lean_panic_fn_borrowed(v___x_315_, v_msg_303_);
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v___y_305_);
lean_inc(v___y_304_);
v___x_317_ = lean_apply_11(v___x_3860__overap_316_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, lean_box(0));
return v___x_317_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_303_ = stack[0].m_obj;
lean_object* v___y_304_ = stack[1].m_obj;
lean_object* v___y_305_ = stack[2].m_obj;
lean_object* v___y_306_ = stack[3].m_obj;
lean_object* v___y_307_ = stack[4].m_obj;
lean_object* v___y_308_ = stack[5].m_obj;
lean_object* v___y_309_ = stack[6].m_obj;
lean_object* v___y_310_ = stack[7].m_obj;
lean_object* v___y_311_ = stack[8].m_obj;
lean_object* v___y_312_ = stack[9].m_obj;
lean_object* v___y_313_ = stack[10].m_obj;
lean_object* v_res_318_;
v_res_318_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v_msg_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___boxed(lean_object* v_msg_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v_msg_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec(v___y_320_);
return v_res_331_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1));
v___x_335_ = lean_unsigned_to_nat(6u);
v___x_336_ = lean_unsigned_to_nat(49u);
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_338_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_339_ = l_mkPanicMessageWithDecl(v___x_338_, v___x_337_, v___x_336_, v___x_335_, v___x_334_);
return v___x_339_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_340_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_341_ = lean_unsigned_to_nat(30u);
v___x_342_ = lean_unsigned_to_nat(48u);
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_344_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_345_ = l_mkPanicMessageWithDecl(v___x_344_, v___x_343_, v___x_342_, v___x_341_, v___x_340_);
return v___x_345_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object* v_____s_346_, uint8_t v_isLower_347_, lean_object* v_as_348_, size_t v_sz_349_, size_t v_i_350_, lean_object* v_b_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_lt(v_i_350_, v_sz_349_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_b_351_);
return v___x_364_;
}
else
{
lean_object* v_snd_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_440_; 
v_snd_365_ = lean_ctor_get(v_b_351_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v_b_351_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v_b_351_, 0);
lean_dec(v_unused_441_);
v___x_367_ = v_b_351_;
v_isShared_368_ = v_isSharedCheck_440_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_snd_365_);
lean_dec(v_b_351_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_440_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_a_369_; lean_object* v_p_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_438_; 
v_a_369_ = lean_array_uget(v_as_348_, v_i_350_);
v_p_370_ = lean_ctor_get(v_a_369_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_a_369_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v_a_369_, 1);
lean_dec(v_unused_439_);
v___x_372_ = v_a_369_;
v_isShared_373_ = v_isSharedCheck_438_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_p_370_);
lean_dec(v_a_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_438_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v_a_376_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_374_ = lean_box(0);
v___x_383_ = lean_box(0);
v___x_384_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_370_, v_____s_346_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_384_) == 0)
{
uint8_t v___y_386_; 
lean_dec_ref_known(v___x_384_, 1);
if (lean_obj_tag(v_p_370_) == 1)
{
lean_object* v_k_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_k_417_ = lean_ctor_get(v_p_370_, 0);
lean_inc(v_k_417_);
lean_dec_ref_known(v_p_370_, 3);
v___x_418_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_419_ = lean_int_dec_lt(v_k_417_, v___x_418_);
lean_dec(v_k_417_);
if (v___x_419_ == 0)
{
if (v_isLower_347_ == 0)
{
v___y_386_ = v___x_363_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___x_419_;
goto v___jp_385_;
}
}
else
{
v___y_386_ = v_isLower_347_;
goto v___jp_385_;
}
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_del_object(v___x_372_);
lean_dec_ref(v_p_370_);
lean_dec(v_snd_365_);
v___x_420_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_421_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_420_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_dec_ref_known(v___x_421_, 1);
v_a_376_ = v___x_383_;
goto v___jp_375_;
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_del_object(v___x_367_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
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
v___jp_385_:
{
if (v___y_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_388_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_387_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_408_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_408_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_408_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_408_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
if (lean_obj_tag(v_a_389_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_406_; 
lean_del_object(v___x_367_);
v_a_393_ = lean_ctor_get(v_a_389_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_a_389_);
if (v_isSharedCheck_406_ == 0)
{
v___x_395_ = v_a_389_;
v_isShared_396_ = v_isSharedCheck_406_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_a_389_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_406_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 1);
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_405_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v_snd_365_);
lean_ctor_set(v___x_372_, 0, v___x_398_);
v___x_400_ = v___x_372_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_snd_365_);
v___x_400_ = v_reuseFailAlloc_404_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_400_);
v___x_402_ = v___x_391_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
else
{
lean_object* v_a_407_; 
lean_del_object(v___x_391_);
lean_del_object(v___x_372_);
lean_dec(v_snd_365_);
v_a_407_ = lean_ctor_get(v_a_389_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v_a_389_, 1);
v_a_376_ = v_a_407_;
goto v___jp_375_;
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_del_object(v___x_372_);
lean_del_object(v___x_367_);
lean_dec(v_snd_365_);
v_a_409_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_388_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_388_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_del_object(v___x_372_);
lean_dec(v_snd_365_);
v_a_376_ = v___x_383_;
goto v___jp_375_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_del_object(v___x_372_);
lean_dec_ref(v_p_370_);
lean_del_object(v___x_367_);
lean_dec(v_snd_365_);
v_a_430_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_384_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_384_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
v___jp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v_a_376_);
lean_ctor_set(v___x_367_, 0, v___x_374_);
v___x_378_ = v___x_367_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_a_376_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
size_t v___x_379_; size_t v___x_380_; 
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_350_, v___x_379_);
v_i_350_ = v___x_380_;
v_b_351_ = v___x_378_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_346_ = stack[0].m_obj;
uint8_t v_isLower_347_ = stack[1].m_num;
lean_object* v_as_348_ = stack[2].m_obj;
size_t v_sz_349_ = stack[3].m_num;
size_t v_i_350_ = stack[4].m_num;
lean_object* v_b_351_ = stack[5].m_obj;
lean_object* v___y_352_ = stack[6].m_obj;
lean_object* v___y_353_ = stack[7].m_obj;
lean_object* v___y_354_ = stack[8].m_obj;
lean_object* v___y_355_ = stack[9].m_obj;
lean_object* v___y_356_ = stack[10].m_obj;
lean_object* v___y_357_ = stack[11].m_obj;
lean_object* v___y_358_ = stack[12].m_obj;
lean_object* v___y_359_ = stack[13].m_obj;
lean_object* v___y_360_ = stack[14].m_obj;
lean_object* v___y_361_ = stack[15].m_obj;
lean_object* v_res_442_;
v_res_442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_346_, v_isLower_347_, v_as_348_, v_sz_349_, v_i_350_, v_b_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_____s_443_ = _args[0];
lean_object* v_isLower_444_ = _args[1];
lean_object* v_as_445_ = _args[2];
lean_object* v_sz_446_ = _args[3];
lean_object* v_i_447_ = _args[4];
lean_object* v_b_448_ = _args[5];
lean_object* v___y_449_ = _args[6];
lean_object* v___y_450_ = _args[7];
lean_object* v___y_451_ = _args[8];
lean_object* v___y_452_ = _args[9];
lean_object* v___y_453_ = _args[10];
lean_object* v___y_454_ = _args[11];
lean_object* v___y_455_ = _args[12];
lean_object* v___y_456_ = _args[13];
lean_object* v___y_457_ = _args[14];
lean_object* v___y_458_ = _args[15];
lean_object* v___y_459_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_460_; size_t v_sz_boxed_461_; size_t v_i_boxed_462_; lean_object* v_res_463_; 
v_isLower_boxed_460_ = lean_unbox(v_isLower_444_);
v_sz_boxed_461_ = lean_unbox_usize(v_sz_446_);
lean_dec(v_sz_446_);
v_i_boxed_462_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_443_, v_isLower_boxed_460_, v_as_445_, v_sz_boxed_461_, v_i_boxed_462_, v_b_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v_as_445_);
lean_dec(v_____s_443_);
return v_res_463_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(lean_object* v_____s_464_, uint8_t v_isLower_465_, lean_object* v_as_466_, size_t v_sz_467_, size_t v_i_468_, lean_object* v_b_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_lt(v_i_468_, v_sz_467_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_b_469_);
return v___x_482_;
}
else
{
lean_object* v_snd_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_558_; 
v_snd_483_ = lean_ctor_get(v_b_469_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_b_469_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v_b_469_, 0);
lean_dec(v_unused_559_);
v___x_485_ = v_b_469_;
v_isShared_486_ = v_isSharedCheck_558_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_snd_483_);
lean_dec(v_b_469_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_558_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_a_487_; lean_object* v_p_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_556_; 
v_a_487_ = lean_array_uget(v_as_466_, v_i_468_);
v_p_488_ = lean_ctor_get(v_a_487_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_a_487_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_a_487_, 1);
lean_dec(v_unused_557_);
v___x_490_ = v_a_487_;
v_isShared_491_ = v_isSharedCheck_556_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_p_488_);
lean_dec(v_a_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_556_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_a_495_; lean_object* v___x_502_; 
v___x_492_ = lean_box(0);
v___x_493_ = lean_box(0);
v___x_502_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_488_, v_____s_464_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_502_) == 0)
{
uint8_t v___y_504_; 
lean_dec_ref_known(v___x_502_, 1);
if (lean_obj_tag(v_p_488_) == 1)
{
lean_object* v_k_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_k_535_ = lean_ctor_get(v_p_488_, 0);
lean_inc(v_k_535_);
lean_dec_ref_known(v_p_488_, 3);
v___x_536_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_537_ = lean_int_dec_lt(v_k_535_, v___x_536_);
lean_dec(v_k_535_);
if (v___x_537_ == 0)
{
if (v_isLower_465_ == 0)
{
v___y_504_ = v___x_481_;
goto v___jp_503_;
}
else
{
v___y_504_ = v___x_537_;
goto v___jp_503_;
}
}
else
{
v___y_504_ = v_isLower_465_;
goto v___jp_503_;
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_del_object(v___x_490_);
lean_dec_ref(v_p_488_);
lean_dec(v_snd_483_);
v___x_538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_539_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_538_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_dec_ref_known(v___x_539_, 1);
v_a_495_ = v___x_492_;
goto v___jp_494_;
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_485_);
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
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
v___jp_503_:
{
if (v___y_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_506_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_505_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_526_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_526_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_526_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_526_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
if (lean_obj_tag(v_a_507_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_524_; 
lean_del_object(v___x_485_);
v_a_511_ = lean_ctor_get(v_a_507_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_524_ == 0)
{
v___x_513_ = v_a_507_;
v_isShared_514_ = v_isSharedCheck_524_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v_a_507_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_524_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 1);
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_523_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v_snd_483_);
lean_ctor_set(v___x_490_, 0, v___x_516_);
v___x_518_ = v___x_490_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_snd_483_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_518_);
v___x_520_ = v___x_509_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
else
{
lean_object* v_a_525_; 
lean_del_object(v___x_509_);
lean_del_object(v___x_490_);
lean_dec(v_snd_483_);
v_a_525_ = lean_ctor_get(v_a_507_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v_a_507_, 1);
v_a_495_ = v_a_525_;
goto v___jp_494_;
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_del_object(v___x_490_);
lean_del_object(v___x_485_);
lean_dec(v_snd_483_);
v_a_527_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_506_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_506_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_del_object(v___x_490_);
lean_dec(v_snd_483_);
v_a_495_ = v___x_492_;
goto v___jp_494_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_del_object(v___x_490_);
lean_dec_ref(v_p_488_);
lean_del_object(v___x_485_);
lean_dec(v_snd_483_);
v_a_548_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_502_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_502_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
v___jp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v_a_495_);
lean_ctor_set(v___x_485_, 0, v___x_493_);
v___x_497_ = v___x_485_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_a_495_);
v___x_497_ = v_reuseFailAlloc_501_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_468_, v___x_498_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_464_, v_isLower_465_, v_as_466_, v_sz_467_, v___x_499_, v___x_497_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v___x_500_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_464_ = stack[0].m_obj;
uint8_t v_isLower_465_ = stack[1].m_num;
lean_object* v_as_466_ = stack[2].m_obj;
size_t v_sz_467_ = stack[3].m_num;
size_t v_i_468_ = stack[4].m_num;
lean_object* v_b_469_ = stack[5].m_obj;
lean_object* v___y_470_ = stack[6].m_obj;
lean_object* v___y_471_ = stack[7].m_obj;
lean_object* v___y_472_ = stack[8].m_obj;
lean_object* v___y_473_ = stack[9].m_obj;
lean_object* v___y_474_ = stack[10].m_obj;
lean_object* v___y_475_ = stack[11].m_obj;
lean_object* v___y_476_ = stack[12].m_obj;
lean_object* v___y_477_ = stack[13].m_obj;
lean_object* v___y_478_ = stack[14].m_obj;
lean_object* v___y_479_ = stack[15].m_obj;
lean_object* v_res_560_;
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_464_, v_isLower_465_, v_as_466_, v_sz_467_, v_i_468_, v_b_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_561_ = _args[0];
lean_object* v_isLower_562_ = _args[1];
lean_object* v_as_563_ = _args[2];
lean_object* v_sz_564_ = _args[3];
lean_object* v_i_565_ = _args[4];
lean_object* v_b_566_ = _args[5];
lean_object* v___y_567_ = _args[6];
lean_object* v___y_568_ = _args[7];
lean_object* v___y_569_ = _args[8];
lean_object* v___y_570_ = _args[9];
lean_object* v___y_571_ = _args[10];
lean_object* v___y_572_ = _args[11];
lean_object* v___y_573_ = _args[12];
lean_object* v___y_574_ = _args[13];
lean_object* v___y_575_ = _args[14];
lean_object* v___y_576_ = _args[15];
lean_object* v___y_577_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_578_; size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_isLower_boxed_578_ = lean_unbox(v_isLower_562_);
v_sz_boxed_579_ = lean_unbox_usize(v_sz_564_);
lean_dec(v_sz_564_);
v_i_boxed_580_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_561_, v_isLower_boxed_578_, v_as_563_, v_sz_boxed_579_, v_i_boxed_580_, v_b_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v_as_563_);
lean_dec(v_____s_561_);
return v_res_581_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object* v_____s_582_, uint8_t v_isLower_583_, lean_object* v_as_584_, size_t v_sz_585_, size_t v_i_586_, lean_object* v_b_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = lean_usize_dec_lt(v_i_586_, v_sz_585_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_b_587_);
return v___x_600_;
}
else
{
lean_object* v_snd_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_669_; 
v_snd_601_ = lean_ctor_get(v_b_587_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_b_587_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_b_587_, 0);
lean_dec(v_unused_670_);
v___x_603_ = v_b_587_;
v_isShared_604_ = v_isSharedCheck_669_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_snd_601_);
lean_dec(v_b_587_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_669_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_a_605_; lean_object* v_p_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_667_; 
v_a_605_ = lean_array_uget(v_as_584_, v_i_586_);
v_p_606_ = lean_ctor_get(v_a_605_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_a_605_, 1);
lean_dec(v_unused_668_);
v___x_608_ = v_a_605_;
v_isShared_609_ = v_isSharedCheck_667_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_p_606_);
lean_dec(v_a_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_667_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v_a_612_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_610_ = lean_box(0);
v___x_619_ = lean_box(0);
v___x_620_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_606_, v_____s_582_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_620_) == 0)
{
uint8_t v___y_622_; 
lean_dec_ref_known(v___x_620_, 1);
if (lean_obj_tag(v_p_606_) == 1)
{
lean_object* v_k_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_k_646_ = lean_ctor_get(v_p_606_, 0);
lean_inc(v_k_646_);
lean_dec_ref_known(v_p_606_, 3);
v___x_647_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_648_ = lean_int_dec_lt(v_k_646_, v___x_647_);
lean_dec(v_k_646_);
if (v___x_648_ == 0)
{
if (v_isLower_583_ == 0)
{
v___y_622_ = v___x_599_;
goto v___jp_621_;
}
else
{
v___y_622_ = v___x_648_;
goto v___jp_621_;
}
}
else
{
v___y_622_ = v_isLower_583_;
goto v___jp_621_;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_608_);
lean_dec_ref(v_p_606_);
lean_dec(v_snd_601_);
v___x_649_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_650_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_649_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_dec_ref_known(v___x_650_, 1);
v_a_612_ = v___x_619_;
goto v___jp_611_;
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_del_object(v___x_603_);
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
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
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_624_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_623_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_637_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_637_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_637_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_637_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
if (lean_obj_tag(v_a_625_) == 0)
{
lean_object* v___x_629_; lean_object* v___x_631_; 
lean_del_object(v___x_603_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v_a_625_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v_snd_601_);
lean_ctor_set(v___x_608_, 0, v___x_629_);
v___x_631_ = v___x_608_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_snd_601_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_631_);
v___x_633_ = v___x_627_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v_a_636_; 
lean_del_object(v___x_627_);
lean_del_object(v___x_608_);
lean_dec(v_snd_601_);
v_a_636_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v_a_625_, 1);
v_a_612_ = v_a_636_;
goto v___jp_611_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_del_object(v___x_608_);
lean_del_object(v___x_603_);
lean_dec(v_snd_601_);
v_a_638_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_624_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_624_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_del_object(v___x_608_);
lean_dec(v_snd_601_);
v_a_612_ = v___x_619_;
goto v___jp_611_;
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_del_object(v___x_608_);
lean_dec_ref(v_p_606_);
lean_del_object(v___x_603_);
lean_dec(v_snd_601_);
v_a_659_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_620_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_620_);
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
v___jp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_a_612_);
lean_ctor_set(v___x_603_, 0, v___x_610_);
v___x_614_ = v___x_603_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_a_612_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
size_t v___x_615_; size_t v___x_616_; 
v___x_615_ = ((size_t)1ULL);
v___x_616_ = lean_usize_add(v_i_586_, v___x_615_);
v_i_586_ = v___x_616_;
v_b_587_ = v___x_614_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_582_ = stack[0].m_obj;
uint8_t v_isLower_583_ = stack[1].m_num;
lean_object* v_as_584_ = stack[2].m_obj;
size_t v_sz_585_ = stack[3].m_num;
size_t v_i_586_ = stack[4].m_num;
lean_object* v_b_587_ = stack[5].m_obj;
lean_object* v___y_588_ = stack[6].m_obj;
lean_object* v___y_589_ = stack[7].m_obj;
lean_object* v___y_590_ = stack[8].m_obj;
lean_object* v___y_591_ = stack[9].m_obj;
lean_object* v___y_592_ = stack[10].m_obj;
lean_object* v___y_593_ = stack[11].m_obj;
lean_object* v___y_594_ = stack[12].m_obj;
lean_object* v___y_595_ = stack[13].m_obj;
lean_object* v___y_596_ = stack[14].m_obj;
lean_object* v___y_597_ = stack[15].m_obj;
lean_object* v_res_671_;
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_582_, v_isLower_583_, v_as_584_, v_sz_585_, v_i_586_, v_b_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_____s_672_ = _args[0];
lean_object* v_isLower_673_ = _args[1];
lean_object* v_as_674_ = _args[2];
lean_object* v_sz_675_ = _args[3];
lean_object* v_i_676_ = _args[4];
lean_object* v_b_677_ = _args[5];
lean_object* v___y_678_ = _args[6];
lean_object* v___y_679_ = _args[7];
lean_object* v___y_680_ = _args[8];
lean_object* v___y_681_ = _args[9];
lean_object* v___y_682_ = _args[10];
lean_object* v___y_683_ = _args[11];
lean_object* v___y_684_ = _args[12];
lean_object* v___y_685_ = _args[13];
lean_object* v___y_686_ = _args[14];
lean_object* v___y_687_ = _args[15];
lean_object* v___y_688_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_689_; size_t v_sz_boxed_690_; size_t v_i_boxed_691_; lean_object* v_res_692_; 
v_isLower_boxed_689_ = lean_unbox(v_isLower_673_);
v_sz_boxed_690_ = lean_unbox_usize(v_sz_675_);
lean_dec(v_sz_675_);
v_i_boxed_691_ = lean_unbox_usize(v_i_676_);
lean_dec(v_i_676_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_672_, v_isLower_boxed_689_, v_as_674_, v_sz_boxed_690_, v_i_boxed_691_, v_b_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v_as_674_);
lean_dec(v_____s_672_);
return v_res_692_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object* v_____s_693_, uint8_t v_isLower_694_, lean_object* v_as_695_, size_t v_sz_696_, size_t v_i_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_lt(v_i_697_, v_sz_696_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_b_698_);
return v___x_711_;
}
else
{
lean_object* v_snd_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_780_; 
v_snd_712_ = lean_ctor_get(v_b_698_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_b_698_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v_b_698_, 0);
lean_dec(v_unused_781_);
v___x_714_ = v_b_698_;
v_isShared_715_ = v_isSharedCheck_780_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snd_712_);
lean_dec(v_b_698_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_780_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_a_716_; lean_object* v_p_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_778_; 
v_a_716_ = lean_array_uget(v_as_695_, v_i_697_);
v_p_717_ = lean_ctor_get(v_a_716_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_a_716_, 1);
lean_dec(v_unused_779_);
v___x_719_ = v_a_716_;
v_isShared_720_ = v_isSharedCheck_778_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_p_717_);
lean_dec(v_a_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_778_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_a_724_; lean_object* v___x_731_; 
v___x_721_ = lean_box(0);
v___x_722_ = lean_box(0);
v___x_731_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_717_, v_____s_693_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_731_) == 0)
{
uint8_t v___y_733_; 
lean_dec_ref_known(v___x_731_, 1);
if (lean_obj_tag(v_p_717_) == 1)
{
lean_object* v_k_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_k_757_ = lean_ctor_get(v_p_717_, 0);
lean_inc(v_k_757_);
lean_dec_ref_known(v_p_717_, 3);
v___x_758_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_759_ = lean_int_dec_lt(v_k_757_, v___x_758_);
lean_dec(v_k_757_);
if (v___x_759_ == 0)
{
if (v_isLower_694_ == 0)
{
v___y_733_ = v___x_710_;
goto v___jp_732_;
}
else
{
v___y_733_ = v___x_759_;
goto v___jp_732_;
}
}
else
{
v___y_733_ = v_isLower_694_;
goto v___jp_732_;
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_del_object(v___x_719_);
lean_dec_ref(v_p_717_);
lean_dec(v_snd_712_);
v___x_760_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_761_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_760_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_dec_ref_known(v___x_761_, 1);
v_a_724_ = v___x_721_;
goto v___jp_723_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_del_object(v___x_714_);
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
v___jp_732_:
{
if (v___y_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_735_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_734_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_748_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_748_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_748_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
if (lean_obj_tag(v_a_736_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_del_object(v___x_714_);
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v_a_736_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_snd_712_);
lean_ctor_set(v___x_719_, 0, v___x_740_);
v___x_742_ = v___x_719_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_snd_712_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_742_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v_a_747_; 
lean_del_object(v___x_738_);
lean_del_object(v___x_719_);
lean_dec(v_snd_712_);
v_a_747_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v_a_736_, 1);
v_a_724_ = v_a_747_;
goto v___jp_723_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_del_object(v___x_719_);
lean_del_object(v___x_714_);
lean_dec(v_snd_712_);
v_a_749_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_735_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_735_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_del_object(v___x_719_);
lean_dec(v_snd_712_);
v_a_724_ = v___x_721_;
goto v___jp_723_;
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_719_);
lean_dec_ref(v_p_717_);
lean_del_object(v___x_714_);
lean_dec(v_snd_712_);
v_a_770_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_731_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_731_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
v___jp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_a_724_);
lean_ctor_set(v___x_714_, 0, v___x_722_);
v___x_726_ = v___x_714_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_a_724_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_697_, v___x_727_);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_693_, v_isLower_694_, v_as_695_, v_sz_696_, v___x_728_, v___x_726_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_729_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_693_ = stack[0].m_obj;
uint8_t v_isLower_694_ = stack[1].m_num;
lean_object* v_as_695_ = stack[2].m_obj;
size_t v_sz_696_ = stack[3].m_num;
size_t v_i_697_ = stack[4].m_num;
lean_object* v_b_698_ = stack[5].m_obj;
lean_object* v___y_699_ = stack[6].m_obj;
lean_object* v___y_700_ = stack[7].m_obj;
lean_object* v___y_701_ = stack[8].m_obj;
lean_object* v___y_702_ = stack[9].m_obj;
lean_object* v___y_703_ = stack[10].m_obj;
lean_object* v___y_704_ = stack[11].m_obj;
lean_object* v___y_705_ = stack[12].m_obj;
lean_object* v___y_706_ = stack[13].m_obj;
lean_object* v___y_707_ = stack[14].m_obj;
lean_object* v___y_708_ = stack[15].m_obj;
lean_object* v_res_782_;
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_693_, v_isLower_694_, v_as_695_, v_sz_696_, v_i_697_, v_b_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_____s_783_ = _args[0];
lean_object* v_isLower_784_ = _args[1];
lean_object* v_as_785_ = _args[2];
lean_object* v_sz_786_ = _args[3];
lean_object* v_i_787_ = _args[4];
lean_object* v_b_788_ = _args[5];
lean_object* v___y_789_ = _args[6];
lean_object* v___y_790_ = _args[7];
lean_object* v___y_791_ = _args[8];
lean_object* v___y_792_ = _args[9];
lean_object* v___y_793_ = _args[10];
lean_object* v___y_794_ = _args[11];
lean_object* v___y_795_ = _args[12];
lean_object* v___y_796_ = _args[13];
lean_object* v___y_797_ = _args[14];
lean_object* v___y_798_ = _args[15];
lean_object* v___y_799_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_800_; size_t v_sz_boxed_801_; size_t v_i_boxed_802_; lean_object* v_res_803_; 
v_isLower_boxed_800_ = lean_unbox(v_isLower_784_);
v_sz_boxed_801_ = lean_unbox_usize(v_sz_786_);
lean_dec(v_sz_786_);
v_i_boxed_802_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_res_803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_783_, v_isLower_boxed_800_, v_as_785_, v_sz_boxed_801_, v_i_boxed_802_, v_b_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v_as_785_);
lean_dec(v_____s_783_);
return v_res_803_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(lean_object* v_init_804_, lean_object* v_____s_805_, uint8_t v_isLower_806_, lean_object* v_n_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
if (lean_obj_tag(v_n_807_) == 0)
{
lean_object* v_cs_820_; lean_object* v___x_821_; lean_object* v___x_822_; size_t v_sz_823_; size_t v___x_824_; lean_object* v___x_825_; 
v_cs_820_ = lean_ctor_get(v_n_807_, 0);
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v_b_808_);
v_sz_823_ = lean_array_size(v_cs_820_);
v___x_824_ = ((size_t)0ULL);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_804_, v_____s_805_, v_isLower_806_, v_cs_820_, v_sz_823_, v___x_824_, v___x_822_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_840_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_840_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_840_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_840_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_fst_830_; 
v_fst_830_ = lean_ctor_get(v_a_826_, 0);
if (lean_obj_tag(v_fst_830_) == 0)
{
lean_object* v_snd_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v_snd_831_ = lean_ctor_get(v_a_826_, 1);
lean_inc(v_snd_831_);
lean_dec(v_a_826_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v_snd_831_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_832_);
v___x_834_ = v___x_828_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
lean_object* v_val_836_; lean_object* v___x_838_; 
lean_inc_ref(v_fst_830_);
lean_dec(v_a_826_);
v_val_836_ = lean_ctor_get(v_fst_830_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v_fst_830_, 1);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_val_836_);
v___x_838_ = v___x_828_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_val_836_);
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
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_a_841_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_825_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_825_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_vs_849_; lean_object* v___x_850_; lean_object* v___x_851_; size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; 
v_vs_849_ = lean_ctor_get(v_n_807_, 0);
v___x_850_ = lean_box(0);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_b_808_);
v_sz_852_ = lean_array_size(v_vs_849_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_805_, v_isLower_806_, v_vs_849_, v_sz_852_, v___x_853_, v___x_851_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_869_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_869_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_fst_859_; 
v_fst_859_ = lean_ctor_get(v_a_855_, 0);
if (lean_obj_tag(v_fst_859_) == 0)
{
lean_object* v_snd_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v_snd_860_ = lean_ctor_get(v_a_855_, 1);
lean_inc(v_snd_860_);
lean_dec(v_a_855_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_snd_860_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_861_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
else
{
lean_object* v_val_865_; lean_object* v___x_867_; 
lean_inc_ref(v_fst_859_);
lean_dec(v_a_855_);
v_val_865_ = lean_ctor_get(v_fst_859_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v_fst_859_, 1);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v_val_865_);
v___x_867_ = v___x_857_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_val_865_);
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
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_854_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_854_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_804_ = stack[0].m_obj;
lean_object* v_____s_805_ = stack[1].m_obj;
uint8_t v_isLower_806_ = stack[2].m_num;
lean_object* v_n_807_ = stack[3].m_obj;
lean_object* v_b_808_ = stack[4].m_obj;
lean_object* v___y_809_ = stack[5].m_obj;
lean_object* v___y_810_ = stack[6].m_obj;
lean_object* v___y_811_ = stack[7].m_obj;
lean_object* v___y_812_ = stack[8].m_obj;
lean_object* v___y_813_ = stack[9].m_obj;
lean_object* v___y_814_ = stack[10].m_obj;
lean_object* v___y_815_ = stack[11].m_obj;
lean_object* v___y_816_ = stack[12].m_obj;
lean_object* v___y_817_ = stack[13].m_obj;
lean_object* v___y_818_ = stack[14].m_obj;
lean_object* v_res_878_;
v_res_878_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_804_, v_____s_805_, v_isLower_806_, v_n_807_, v_b_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
stack->m_obj
 = v_res_878_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_init_879_, lean_object* v_____s_880_, uint8_t v_isLower_881_, lean_object* v_as_882_, size_t v_sz_883_, size_t v_i_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_lt(v_i_884_, v_sz_883_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_b_885_);
return v___x_898_;
}
else
{
lean_object* v_snd_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_933_; 
v_snd_899_ = lean_ctor_get(v_b_885_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_b_885_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v_b_885_, 0);
lean_dec(v_unused_934_);
v___x_901_ = v_b_885_;
v_isShared_902_ = v_isSharedCheck_933_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snd_899_);
lean_dec(v_b_885_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_933_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v_a_904_; lean_object* v___x_905_; 
v___x_903_ = lean_box(0);
v_a_904_ = lean_array_uget_borrowed(v_as_882_, v_i_884_);
lean_inc(v_snd_899_);
v___x_905_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_879_, v_____s_880_, v_isLower_881_, v_a_904_, v_snd_899_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_924_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_924_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_924_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_924_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
if (lean_obj_tag(v_a_906_) == 0)
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v_a_906_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_910_);
v___x_912_ = v___x_901_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_snd_899_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_912_);
v___x_914_ = v___x_908_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; 
lean_del_object(v___x_908_);
lean_dec(v_snd_899_);
v_a_917_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v_a_906_, 1);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v_a_917_);
lean_ctor_set(v___x_901_, 0, v___x_903_);
v___x_919_ = v___x_901_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_a_917_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
size_t v___x_920_; size_t v___x_921_; 
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_add(v_i_884_, v___x_920_);
v_i_884_ = v___x_921_;
v_b_885_ = v___x_919_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
v_a_925_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_905_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_905_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_879_ = stack[0].m_obj;
lean_object* v_____s_880_ = stack[1].m_obj;
uint8_t v_isLower_881_ = stack[2].m_num;
lean_object* v_as_882_ = stack[3].m_obj;
size_t v_sz_883_ = stack[4].m_num;
size_t v_i_884_ = stack[5].m_num;
lean_object* v_b_885_ = stack[6].m_obj;
lean_object* v___y_886_ = stack[7].m_obj;
lean_object* v___y_887_ = stack[8].m_obj;
lean_object* v___y_888_ = stack[9].m_obj;
lean_object* v___y_889_ = stack[10].m_obj;
lean_object* v___y_890_ = stack[11].m_obj;
lean_object* v___y_891_ = stack[12].m_obj;
lean_object* v___y_892_ = stack[13].m_obj;
lean_object* v___y_893_ = stack[14].m_obj;
lean_object* v___y_894_ = stack[15].m_obj;
lean_object* v___y_895_ = stack[16].m_obj;
lean_object* v_res_935_;
v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_879_, v_____s_880_, v_isLower_881_, v_as_882_, v_sz_883_, v_i_884_, v_b_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
stack->m_obj
 = v_res_935_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_936_ = _args[0];
lean_object* v_____s_937_ = _args[1];
lean_object* v_isLower_938_ = _args[2];
lean_object* v_as_939_ = _args[3];
lean_object* v_sz_940_ = _args[4];
lean_object* v_i_941_ = _args[5];
lean_object* v_b_942_ = _args[6];
lean_object* v___y_943_ = _args[7];
lean_object* v___y_944_ = _args[8];
lean_object* v___y_945_ = _args[9];
lean_object* v___y_946_ = _args[10];
lean_object* v___y_947_ = _args[11];
lean_object* v___y_948_ = _args[12];
lean_object* v___y_949_ = _args[13];
lean_object* v___y_950_ = _args[14];
lean_object* v___y_951_ = _args[15];
lean_object* v___y_952_ = _args[16];
lean_object* v___y_953_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_954_; size_t v_sz_boxed_955_; size_t v_i_boxed_956_; lean_object* v_res_957_; 
v_isLower_boxed_954_ = lean_unbox(v_isLower_938_);
v_sz_boxed_955_ = lean_unbox_usize(v_sz_940_);
lean_dec(v_sz_940_);
v_i_boxed_956_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_936_, v_____s_937_, v_isLower_boxed_954_, v_as_939_, v_sz_boxed_955_, v_i_boxed_956_, v_b_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v_as_939_);
lean_dec(v_____s_937_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1___boxed(lean_object* v_init_958_, lean_object* v_____s_959_, lean_object* v_isLower_960_, lean_object* v_n_961_, lean_object* v_b_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
uint8_t v_isLower_boxed_974_; lean_object* v_res_975_; 
v_isLower_boxed_974_ = lean_unbox(v_isLower_960_);
v_res_975_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_958_, v_____s_959_, v_isLower_boxed_974_, v_n_961_, v_b_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v_n_961_);
lean_dec(v_____s_959_);
return v_res_975_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(lean_object* v_____s_976_, uint8_t v_isLower_977_, lean_object* v_t_978_, lean_object* v_init_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_root_991_; lean_object* v_tail_992_; lean_object* v___x_993_; 
v_root_991_ = lean_ctor_get(v_t_978_, 0);
v_tail_992_ = lean_ctor_get(v_t_978_, 1);
v___x_993_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_979_, v_____s_976_, v_isLower_977_, v_root_991_, v_init_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1030_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1030_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1030_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
if (lean_obj_tag(v_a_994_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; 
v_a_998_ = lean_ctor_get(v_a_994_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v_a_994_, 1);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_a_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; size_t v_sz_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
lean_del_object(v___x_996_);
v_a_1002_ = lean_ctor_get(v_a_994_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v_a_994_, 1);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_a_1002_);
v_sz_1005_ = lean_array_size(v_tail_992_);
v___x_1006_ = ((size_t)0ULL);
v___x_1007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_976_, v_isLower_977_, v_tail_992_, v_sz_1005_, v___x_1006_, v___x_1004_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1021_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1021_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1021_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_fst_1012_; 
v_fst_1012_ = lean_ctor_get(v_a_1008_, 0);
if (lean_obj_tag(v_fst_1012_) == 0)
{
lean_object* v_snd_1013_; lean_object* v___x_1015_; 
v_snd_1013_ = lean_ctor_get(v_a_1008_, 1);
lean_inc(v_snd_1013_);
lean_dec(v_a_1008_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_snd_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_snd_1013_);
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
lean_object* v_val_1017_; lean_object* v___x_1019_; 
lean_inc_ref(v_fst_1012_);
lean_dec(v_a_1008_);
v_val_1017_ = lean_ctor_get(v_fst_1012_, 0);
lean_inc(v_val_1017_);
lean_dec_ref_known(v_fst_1012_, 1);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_val_1017_);
v___x_1019_ = v___x_1010_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_val_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1007_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1007_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_993_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_993_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_976_ = stack[0].m_obj;
uint8_t v_isLower_977_ = stack[1].m_num;
lean_object* v_t_978_ = stack[2].m_obj;
lean_object* v_init_979_ = stack[3].m_obj;
lean_object* v___y_980_ = stack[4].m_obj;
lean_object* v___y_981_ = stack[5].m_obj;
lean_object* v___y_982_ = stack[6].m_obj;
lean_object* v___y_983_ = stack[7].m_obj;
lean_object* v___y_984_ = stack[8].m_obj;
lean_object* v___y_985_ = stack[9].m_obj;
lean_object* v___y_986_ = stack[10].m_obj;
lean_object* v___y_987_ = stack[11].m_obj;
lean_object* v___y_988_ = stack[12].m_obj;
lean_object* v___y_989_ = stack[13].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_____s_976_, v_isLower_977_, v_t_978_, v_init_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1040_, lean_object* v_isLower_1041_, lean_object* v_t_1042_, lean_object* v_init_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v_isLower_boxed_1055_; lean_object* v_res_1056_; 
v_isLower_boxed_1055_ = lean_unbox(v_isLower_1041_);
v_res_1056_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_____s_1040_, v_isLower_boxed_1055_, v_t_1042_, v_init_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v_t_1042_);
lean_dec(v_____s_1040_);
return v_res_1056_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1057_, lean_object* v_as_1058_, size_t v_sz_1059_, size_t v_i_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_usize_dec_lt(v_i_1060_, v_sz_1059_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_b_1061_);
return v___x_1074_;
}
else
{
lean_object* v_snd_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1099_; 
v_snd_1075_ = lean_ctor_get(v_b_1061_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_b_1061_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v_b_1061_, 0);
lean_dec(v_unused_1100_);
v___x_1077_ = v_b_1061_;
v_isShared_1078_ = v_isSharedCheck_1099_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_snd_1075_);
lean_dec(v_b_1061_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1099_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = lean_box(0);
v_a_1080_ = lean_array_uget_borrowed(v_as_1058_, v_i_1060_);
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1075_, v_isLower_1057_, v_a_1080_, v___x_1081_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_dec_ref_known(v___x_1082_, 1);
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_nat_add(v_snd_1075_, v___x_1083_);
lean_dec(v_snd_1075_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1084_);
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1086_ = v___x_1077_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
size_t v___x_1087_; size_t v___x_1088_; 
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_add(v_i_1060_, v___x_1087_);
v_i_1060_ = v___x_1088_;
v_b_1061_ = v___x_1086_;
goto _start;
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_del_object(v___x_1077_);
lean_dec(v_snd_1075_);
v_a_1091_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1082_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1082_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
uint8_t v_isLower_1057_ = stack[0].m_num;
lean_object* v_as_1058_ = stack[1].m_obj;
size_t v_sz_1059_ = stack[2].m_num;
size_t v_i_1060_ = stack[3].m_num;
lean_object* v_b_1061_ = stack[4].m_obj;
lean_object* v___y_1062_ = stack[5].m_obj;
lean_object* v___y_1063_ = stack[6].m_obj;
lean_object* v___y_1064_ = stack[7].m_obj;
lean_object* v___y_1065_ = stack[8].m_obj;
lean_object* v___y_1066_ = stack[9].m_obj;
lean_object* v___y_1067_ = stack[10].m_obj;
lean_object* v___y_1068_ = stack[11].m_obj;
lean_object* v___y_1069_ = stack[12].m_obj;
lean_object* v___y_1070_ = stack[13].m_obj;
lean_object* v___y_1071_ = stack[14].m_obj;
lean_object* v_res_1101_;
v_res_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1057_, v_as_1058_, v_sz_1059_, v_i_1060_, v_b_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
stack->m_obj
 = v_res_1101_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1122_, lean_object* v_as_1123_, size_t v_sz_1124_, size_t v_i_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
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
lean_object* v___x_1144_; lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_box(0);
v_a_1145_ = lean_array_uget_borrowed(v_as_1123_, v_i_1125_);
v___x_1146_ = lean_box(0);
v___x_1147_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1140_, v_isLower_1122_, v_a_1145_, v___x_1146_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec_ref_known(v___x_1147_, 1);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_snd_1140_, v___x_1148_);
lean_dec(v_snd_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1149_);
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1151_ = v___x_1142_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1144_);
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
v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1147_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1147_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_isLower_1122_ = stack[0].m_num;
lean_object* v_as_1123_ = stack[1].m_obj;
size_t v_sz_1124_ = stack[2].m_num;
size_t v_i_1125_ = stack[3].m_num;
lean_object* v_b_1126_ = stack[4].m_obj;
lean_object* v___y_1127_ = stack[5].m_obj;
lean_object* v___y_1128_ = stack[6].m_obj;
lean_object* v___y_1129_ = stack[7].m_obj;
lean_object* v___y_1130_ = stack[8].m_obj;
lean_object* v___y_1131_ = stack[9].m_obj;
lean_object* v___y_1132_ = stack[10].m_obj;
lean_object* v___y_1133_ = stack[11].m_obj;
lean_object* v___y_1134_ = stack[12].m_obj;
lean_object* v___y_1135_ = stack[13].m_obj;
lean_object* v___y_1136_ = stack[14].m_obj;
lean_object* v_res_1166_;
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_1122_, v_as_1123_, v_sz_1124_, v_i_1125_, v_b_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
stack->m_obj
 = v_res_1166_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5___boxed(lean_object* v_isLower_1167_, lean_object* v_as_1168_, lean_object* v_sz_1169_, lean_object* v_i_1170_, lean_object* v_b_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_isLower_boxed_1183_; size_t v_sz_boxed_1184_; size_t v_i_boxed_1185_; lean_object* v_res_1186_; 
v_isLower_boxed_1183_ = lean_unbox(v_isLower_1167_);
v_sz_boxed_1184_ = lean_unbox_usize(v_sz_1169_);
lean_dec(v_sz_1169_);
v_i_boxed_1185_ = lean_unbox_usize(v_i_1170_);
lean_dec(v_i_1170_);
v_res_1186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1183_, v_as_1168_, v_sz_boxed_1184_, v_i_boxed_1185_, v_b_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v_as_1168_);
return v_res_1186_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1187_, lean_object* v_as_1188_, size_t v_sz_1189_, size_t v_i_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_usize_dec_lt(v_i_1190_, v_sz_1189_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v_b_1191_);
return v___x_1204_;
}
else
{
lean_object* v_snd_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1229_; 
v_snd_1205_ = lean_ctor_get(v_b_1191_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_b_1191_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v_b_1191_, 0);
lean_dec(v_unused_1230_);
v___x_1207_ = v_b_1191_;
v_isShared_1208_ = v_isSharedCheck_1229_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_snd_1205_);
lean_dec(v_b_1191_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1229_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1209_ = lean_box(0);
v_a_1210_ = lean_array_uget_borrowed(v_as_1188_, v_i_1190_);
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1205_, v_isLower_1187_, v_a_1210_, v___x_1211_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_dec_ref_known(v___x_1212_, 1);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = lean_nat_add(v_snd_1205_, v___x_1213_);
lean_dec(v_snd_1205_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1214_);
lean_ctor_set(v___x_1207_, 0, v___x_1209_);
v___x_1216_ = v___x_1207_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
size_t v___x_1217_; size_t v___x_1218_; 
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1190_, v___x_1217_);
v_i_1190_ = v___x_1218_;
v_b_1191_ = v___x_1216_;
goto _start;
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_del_object(v___x_1207_);
lean_dec(v_snd_1205_);
v_a_1221_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1212_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1212_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
uint8_t v_isLower_1187_ = stack[0].m_num;
lean_object* v_as_1188_ = stack[1].m_obj;
size_t v_sz_1189_ = stack[2].m_num;
size_t v_i_1190_ = stack[3].m_num;
lean_object* v_b_1191_ = stack[4].m_obj;
lean_object* v___y_1192_ = stack[5].m_obj;
lean_object* v___y_1193_ = stack[6].m_obj;
lean_object* v___y_1194_ = stack[7].m_obj;
lean_object* v___y_1195_ = stack[8].m_obj;
lean_object* v___y_1196_ = stack[9].m_obj;
lean_object* v___y_1197_ = stack[10].m_obj;
lean_object* v___y_1198_ = stack[11].m_obj;
lean_object* v___y_1199_ = stack[12].m_obj;
lean_object* v___y_1200_ = stack[13].m_obj;
lean_object* v___y_1201_ = stack[14].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1187_, v_as_1188_, v_sz_1189_, v_i_1190_, v_b_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object* v_isLower_1232_, lean_object* v_as_1233_, lean_object* v_sz_1234_, lean_object* v_i_1235_, lean_object* v_b_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v_isLower_boxed_1248_; size_t v_sz_boxed_1249_; size_t v_i_boxed_1250_; lean_object* v_res_1251_; 
v_isLower_boxed_1248_ = lean_unbox(v_isLower_1232_);
v_sz_boxed_1249_ = lean_unbox_usize(v_sz_1234_);
lean_dec(v_sz_1234_);
v_i_boxed_1250_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_res_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1248_, v_as_1233_, v_sz_boxed_1249_, v_i_boxed_1250_, v_b_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v_as_1233_);
return v_res_1251_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1252_, lean_object* v_as_1253_, size_t v_sz_1254_, size_t v_i_1255_, lean_object* v_b_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_usize_dec_lt(v_i_1255_, v_sz_1254_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_b_1256_);
return v___x_1269_;
}
else
{
lean_object* v_snd_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1294_; 
v_snd_1270_ = lean_ctor_get(v_b_1256_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_b_1256_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_b_1256_, 0);
lean_dec(v_unused_1295_);
v___x_1272_ = v_b_1256_;
v_isShared_1273_ = v_isSharedCheck_1294_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_snd_1270_);
lean_dec(v_b_1256_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1294_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1274_ = lean_box(0);
v_a_1275_ = lean_array_uget_borrowed(v_as_1253_, v_i_1255_);
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1270_, v_isLower_1252_, v_a_1275_, v___x_1276_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_dec_ref_known(v___x_1277_, 1);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_add(v_snd_1270_, v___x_1278_);
lean_dec(v_snd_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1279_);
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1281_ = v___x_1272_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = ((size_t)1ULL);
v___x_1283_ = lean_usize_add(v_i_1255_, v___x_1282_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1252_, v_as_1253_, v_sz_1254_, v___x_1283_, v___x_1281_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1284_;
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_del_object(v___x_1272_);
lean_dec(v_snd_1270_);
v_a_1286_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1277_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1277_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v_isLower_1252_ = stack[0].m_num;
lean_object* v_as_1253_ = stack[1].m_obj;
size_t v_sz_1254_ = stack[2].m_num;
size_t v_i_1255_ = stack[3].m_num;
lean_object* v_b_1256_ = stack[4].m_obj;
lean_object* v___y_1257_ = stack[5].m_obj;
lean_object* v___y_1258_ = stack[6].m_obj;
lean_object* v___y_1259_ = stack[7].m_obj;
lean_object* v___y_1260_ = stack[8].m_obj;
lean_object* v___y_1261_ = stack[9].m_obj;
lean_object* v___y_1262_ = stack[10].m_obj;
lean_object* v___y_1263_ = stack[11].m_obj;
lean_object* v___y_1264_ = stack[12].m_obj;
lean_object* v___y_1265_ = stack[13].m_obj;
lean_object* v___y_1266_ = stack[14].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1252_, v_as_1253_, v_sz_1254_, v_i_1255_, v_b_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object* v_isLower_1297_, lean_object* v_as_1298_, lean_object* v_sz_1299_, lean_object* v_i_1300_, lean_object* v_b_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_isLower_boxed_1313_; size_t v_sz_boxed_1314_; size_t v_i_boxed_1315_; lean_object* v_res_1316_; 
v_isLower_boxed_1313_ = lean_unbox(v_isLower_1297_);
v_sz_boxed_1314_ = lean_unbox_usize(v_sz_1299_);
lean_dec(v_sz_1299_);
v_i_boxed_1315_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1313_, v_as_1298_, v_sz_boxed_1314_, v_i_boxed_1315_, v_b_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v_as_1298_);
return v_res_1316_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(lean_object* v_init_1317_, uint8_t v_isLower_1318_, lean_object* v_n_1319_, lean_object* v_b_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
if (lean_obj_tag(v_n_1319_) == 0)
{
lean_object* v_cs_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; size_t v_sz_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v_cs_1332_ = lean_ctor_get(v_n_1319_, 0);
v___x_1333_ = lean_box(0);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v_b_1320_);
v_sz_1335_ = lean_array_size(v_cs_1332_);
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1317_, v_isLower_1318_, v_cs_1332_, v_sz_1335_, v___x_1336_, v___x_1334_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1352_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1352_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1352_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_fst_1342_; 
v_fst_1342_ = lean_ctor_get(v_a_1338_, 0);
if (lean_obj_tag(v_fst_1342_) == 0)
{
lean_object* v_snd_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v_snd_1343_ = lean_ctor_get(v_a_1338_, 1);
lean_inc(v_snd_1343_);
lean_dec(v_a_1338_);
v___x_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_snd_1343_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1344_);
v___x_1346_ = v___x_1340_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
else
{
lean_object* v_val_1348_; lean_object* v___x_1350_; 
lean_inc_ref(v_fst_1342_);
lean_dec(v_a_1338_);
v_val_1348_ = lean_ctor_get(v_fst_1342_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v_fst_1342_, 1);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_val_1348_);
v___x_1350_ = v___x_1340_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_val_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1337_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1337_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_vs_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; size_t v_sz_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v_vs_1361_ = lean_ctor_get(v_n_1319_, 0);
v___x_1362_ = lean_box(0);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v_b_1320_);
v_sz_1364_ = lean_array_size(v_vs_1361_);
v___x_1365_ = ((size_t)0ULL);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1318_, v_vs_1361_, v_sz_1364_, v___x_1365_, v___x_1363_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1381_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1381_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1381_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_fst_1371_; 
v_fst_1371_ = lean_ctor_get(v_a_1367_, 0);
if (lean_obj_tag(v_fst_1371_) == 0)
{
lean_object* v_snd_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v_snd_1372_ = lean_ctor_get(v_a_1367_, 1);
lean_inc(v_snd_1372_);
lean_dec(v_a_1367_);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_snd_1372_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1373_);
v___x_1375_ = v___x_1369_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
lean_object* v_val_1377_; lean_object* v___x_1379_; 
lean_inc_ref(v_fst_1371_);
lean_dec(v_a_1367_);
v_val_1377_ = lean_ctor_get(v_fst_1371_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v_fst_1371_, 1);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v_val_1377_);
v___x_1379_ = v___x_1369_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_val_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
v_a_1382_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1366_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1366_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
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
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1317_ = stack[0].m_obj;
uint8_t v_isLower_1318_ = stack[1].m_num;
lean_object* v_n_1319_ = stack[2].m_obj;
lean_object* v_b_1320_ = stack[3].m_obj;
lean_object* v___y_1321_ = stack[4].m_obj;
lean_object* v___y_1322_ = stack[5].m_obj;
lean_object* v___y_1323_ = stack[6].m_obj;
lean_object* v___y_1324_ = stack[7].m_obj;
lean_object* v___y_1325_ = stack[8].m_obj;
lean_object* v___y_1326_ = stack[9].m_obj;
lean_object* v___y_1327_ = stack[10].m_obj;
lean_object* v___y_1328_ = stack[11].m_obj;
lean_object* v___y_1329_ = stack[12].m_obj;
lean_object* v___y_1330_ = stack[13].m_obj;
lean_object* v_res_1390_;
v_res_1390_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1317_, v_isLower_1318_, v_n_1319_, v_b_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
stack->m_obj
 = v_res_1390_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object* v_init_1391_, uint8_t v_isLower_1392_, lean_object* v_as_1393_, size_t v_sz_1394_, size_t v_i_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_usize_dec_lt(v_i_1395_, v_sz_1394_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_b_1396_);
return v___x_1409_;
}
else
{
lean_object* v_snd_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1444_; 
v_snd_1410_ = lean_ctor_get(v_b_1396_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_b_1396_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v_b_1396_, 0);
lean_dec(v_unused_1445_);
v___x_1412_ = v_b_1396_;
v_isShared_1413_ = v_isSharedCheck_1444_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1410_);
lean_dec(v_b_1396_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1444_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v_a_1415_; lean_object* v___x_1416_; 
v___x_1414_ = lean_box(0);
v_a_1415_ = lean_array_uget_borrowed(v_as_1393_, v_i_1395_);
lean_inc(v_snd_1410_);
v___x_1416_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1391_, v_isLower_1392_, v_a_1415_, v_snd_1410_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1435_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1435_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1435_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
if (lean_obj_tag(v_a_1417_) == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_a_1417_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1421_);
v___x_1423_ = v___x_1412_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_snd_1410_);
v___x_1423_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1423_);
v___x_1425_ = v___x_1419_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; 
lean_del_object(v___x_1419_);
lean_dec(v_snd_1410_);
v_a_1428_ = lean_ctor_get(v_a_1417_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v_a_1417_, 1);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v_a_1428_);
lean_ctor_set(v___x_1412_, 0, v___x_1414_);
v___x_1430_ = v___x_1412_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_a_1428_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
size_t v___x_1431_; size_t v___x_1432_; 
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1395_, v___x_1431_);
v_i_1395_ = v___x_1432_;
v_b_1396_ = v___x_1430_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_del_object(v___x_1412_);
lean_dec(v_snd_1410_);
v_a_1436_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1416_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1416_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1391_ = stack[0].m_obj;
uint8_t v_isLower_1392_ = stack[1].m_num;
lean_object* v_as_1393_ = stack[2].m_obj;
size_t v_sz_1394_ = stack[3].m_num;
size_t v_i_1395_ = stack[4].m_num;
lean_object* v_b_1396_ = stack[5].m_obj;
lean_object* v___y_1397_ = stack[6].m_obj;
lean_object* v___y_1398_ = stack[7].m_obj;
lean_object* v___y_1399_ = stack[8].m_obj;
lean_object* v___y_1400_ = stack[9].m_obj;
lean_object* v___y_1401_ = stack[10].m_obj;
lean_object* v___y_1402_ = stack[11].m_obj;
lean_object* v___y_1403_ = stack[12].m_obj;
lean_object* v___y_1404_ = stack[13].m_obj;
lean_object* v___y_1405_ = stack[14].m_obj;
lean_object* v___y_1406_ = stack[15].m_obj;
lean_object* v_res_1446_;
v_res_1446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1391_, v_isLower_1392_, v_as_1393_, v_sz_1394_, v_i_1395_, v_b_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
stack->m_obj
 = v_res_1446_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_init_1447_ = _args[0];
lean_object* v_isLower_1448_ = _args[1];
lean_object* v_as_1449_ = _args[2];
lean_object* v_sz_1450_ = _args[3];
lean_object* v_i_1451_ = _args[4];
lean_object* v_b_1452_ = _args[5];
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
v_isLower_boxed_1464_ = lean_unbox(v_isLower_1448_);
v_sz_boxed_1465_ = lean_unbox_usize(v_sz_1450_);
lean_dec(v_sz_1450_);
v_i_boxed_1466_ = lean_unbox_usize(v_i_1451_);
lean_dec(v_i_1451_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1447_, v_isLower_boxed_1464_, v_as_1449_, v_sz_boxed_1465_, v_i_boxed_1466_, v_b_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
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
lean_dec_ref(v_as_1449_);
lean_dec(v_init_1447_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_init_1468_, lean_object* v_isLower_1469_, lean_object* v_n_1470_, lean_object* v_b_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v_isLower_boxed_1483_; lean_object* v_res_1484_; 
v_isLower_boxed_1483_ = lean_unbox(v_isLower_1469_);
v_res_1484_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1468_, v_isLower_boxed_1483_, v_n_1470_, v_b_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v_n_1470_);
lean_dec(v_init_1468_);
return v_res_1484_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(uint8_t v_isLower_1485_, lean_object* v_t_1486_, lean_object* v_init_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_root_1499_; lean_object* v_tail_1500_; lean_object* v___x_1501_; 
v_root_1499_ = lean_ctor_get(v_t_1486_, 0);
v_tail_1500_ = lean_ctor_get(v_t_1486_, 1);
lean_inc(v_init_1487_);
v___x_1501_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1487_, v_isLower_1485_, v_root_1499_, v_init_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v_init_1487_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1538_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1538_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1538_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
if (lean_obj_tag(v_a_1502_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; 
v_a_1506_ = lean_ctor_get(v_a_1502_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v_a_1502_, 1);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v_a_1506_);
v___x_1508_ = v___x_1504_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; size_t v_sz_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1504_);
v_a_1510_ = lean_ctor_get(v_a_1502_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v_a_1502_, 1);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v_a_1510_);
v_sz_1513_ = lean_array_size(v_tail_1500_);
v___x_1514_ = ((size_t)0ULL);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_1485_, v_tail_1500_, v_sz_1513_, v___x_1514_, v___x_1512_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1529_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1529_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1529_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_fst_1520_; 
v_fst_1520_ = lean_ctor_get(v_a_1516_, 0);
if (lean_obj_tag(v_fst_1520_) == 0)
{
lean_object* v_snd_1521_; lean_object* v___x_1523_; 
v_snd_1521_ = lean_ctor_get(v_a_1516_, 1);
lean_inc(v_snd_1521_);
lean_dec(v_a_1516_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v_snd_1521_);
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_snd_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
else
{
lean_object* v_val_1525_; lean_object* v___x_1527_; 
lean_inc_ref(v_fst_1520_);
lean_dec(v_a_1516_);
v_val_1525_ = lean_ctor_get(v_fst_1520_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v_fst_1520_, 1);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v_val_1525_);
v___x_1527_ = v___x_1518_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_val_1525_);
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
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
v_a_1530_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1515_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1515_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
v_a_1539_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1501_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1501_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_isLower_1485_ = stack[0].m_num;
lean_object* v_t_1486_ = stack[1].m_obj;
lean_object* v_init_1487_ = stack[2].m_obj;
lean_object* v___y_1488_ = stack[3].m_obj;
lean_object* v___y_1489_ = stack[4].m_obj;
lean_object* v___y_1490_ = stack[5].m_obj;
lean_object* v___y_1491_ = stack[6].m_obj;
lean_object* v___y_1492_ = stack[7].m_obj;
lean_object* v___y_1493_ = stack[8].m_obj;
lean_object* v___y_1494_ = stack[9].m_obj;
lean_object* v___y_1495_ = stack[10].m_obj;
lean_object* v___y_1496_ = stack[11].m_obj;
lean_object* v___y_1497_ = stack[12].m_obj;
lean_object* v_res_1547_;
v_res_1547_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_1485_, v_t_1486_, v_init_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
stack->m_obj
 = v_res_1547_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1548_, lean_object* v_t_1549_, lean_object* v_init_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v_isLower_boxed_1562_; lean_object* v_res_1563_; 
v_isLower_boxed_1562_ = lean_unbox(v_isLower_1548_);
v_res_1563_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_boxed_1562_, v_t_1549_, v_init_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v_t_1549_);
return v_res_1563_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(lean_object* v_css_1564_, uint8_t v_isLower_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_x_1577_; lean_object* v___x_1578_; 
v_x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_1565_, v_css_1564_, v_x_1577_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1586_; 
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v___x_1578_, 0);
lean_dec(v_unused_1587_);
v___x_1580_ = v___x_1578_;
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v___x_1578_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_box(0);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1582_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_a_1588_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1578_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1578_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_0interp(lean_interpreter_value* stack)
{
lean_object* v_css_1564_ = stack[0].m_obj;
uint8_t v_isLower_1565_ = stack[1].m_num;
lean_object* v_a_1566_ = stack[2].m_obj;
lean_object* v_a_1567_ = stack[3].m_obj;
lean_object* v_a_1568_ = stack[4].m_obj;
lean_object* v_a_1569_ = stack[5].m_obj;
lean_object* v_a_1570_ = stack[6].m_obj;
lean_object* v_a_1571_ = stack[7].m_obj;
lean_object* v_a_1572_ = stack[8].m_obj;
lean_object* v_a_1573_ = stack[9].m_obj;
lean_object* v_a_1574_ = stack[10].m_obj;
lean_object* v_a_1575_ = stack[11].m_obj;
lean_object* v_res_1596_;
v_res_1596_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_css_1564_, v_isLower_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
stack->m_obj
 = v_res_1596_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs___boxed(lean_object* v_css_1597_, lean_object* v_isLower_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
uint8_t v_isLower_boxed_1610_; lean_object* v_res_1611_; 
v_isLower_boxed_1610_ = lean_unbox(v_isLower_1598_);
v_res_1611_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_css_1597_, v_isLower_boxed_1610_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_css_1597_);
return v_res_1611_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1));
v___x_1615_ = lean_unsigned_to_nat(2u);
v___x_1616_ = lean_unsigned_to_nat(55u);
v___x_1617_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0));
v___x_1618_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1619_ = l_mkPanicMessageWithDecl(v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_, v___x_1614_);
return v___x_1619_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1620_, v_a_1628_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v_lowers_1633_; lean_object* v_vars_1634_; lean_object* v_size_1635_; lean_object* v_size_1636_; uint8_t v___x_1637_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v_lowers_1633_ = lean_ctor_get(v_a_1632_, 6);
lean_inc_ref(v_lowers_1633_);
v_vars_1634_ = lean_ctor_get(v_a_1632_, 0);
lean_inc_ref(v_vars_1634_);
lean_dec(v_a_1632_);
v_size_1635_ = lean_ctor_get(v_lowers_1633_, 2);
v_size_1636_ = lean_ctor_get(v_vars_1634_, 2);
lean_inc(v_size_1636_);
lean_dec_ref(v_vars_1634_);
v___x_1637_ = lean_nat_dec_eq(v_size_1635_, v_size_1636_);
lean_dec(v_size_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_lowers_1633_);
v___x_1638_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2);
v___x_1639_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_1638_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v___x_1639_;
}
else
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_lowers_1633_, v___x_1637_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
lean_dec_ref(v_lowers_1633_);
return v___x_1640_;
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1631_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1631_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkLowers_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1620_ = stack[0].m_obj;
lean_object* v_a_1621_ = stack[1].m_obj;
lean_object* v_a_1622_ = stack[2].m_obj;
lean_object* v_a_1623_ = stack[3].m_obj;
lean_object* v_a_1624_ = stack[4].m_obj;
lean_object* v_a_1625_ = stack[5].m_obj;
lean_object* v_a_1626_ = stack[6].m_obj;
lean_object* v_a_1627_ = stack[7].m_obj;
lean_object* v_a_1628_ = stack[8].m_obj;
lean_object* v_a_1629_ = stack[9].m_obj;
lean_object* v_res_1649_;
v_res_1649_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
stack->m_obj
 = v_res_1649_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___boxed(lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
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
return v_res_1661_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1664_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1));
v___x_1665_ = lean_unsigned_to_nat(2u);
v___x_1666_ = lean_unsigned_to_nat(60u);
v___x_1667_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0));
v___x_1668_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1669_ = l_mkPanicMessageWithDecl(v___x_1668_, v___x_1667_, v___x_1666_, v___x_1665_, v___x_1664_);
return v___x_1669_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1670_, v_a_1678_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v_uppers_1683_; lean_object* v_vars_1684_; lean_object* v_size_1685_; lean_object* v_size_1686_; uint8_t v___x_1687_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v_uppers_1683_ = lean_ctor_get(v_a_1682_, 7);
lean_inc_ref(v_uppers_1683_);
v_vars_1684_ = lean_ctor_get(v_a_1682_, 0);
lean_inc_ref(v_vars_1684_);
lean_dec(v_a_1682_);
v_size_1685_ = lean_ctor_get(v_uppers_1683_, 2);
v_size_1686_ = lean_ctor_get(v_vars_1684_, 2);
lean_inc(v_size_1686_);
lean_dec_ref(v_vars_1684_);
v___x_1687_ = lean_nat_dec_eq(v_size_1685_, v_size_1686_);
lean_dec(v_size_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_dec_ref(v_uppers_1683_);
v___x_1688_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2);
v___x_1689_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_1688_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
return v___x_1689_;
}
else
{
uint8_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = 0;
v___x_1691_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_uppers_1683_, v___x_1690_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec_ref(v_uppers_1683_);
return v___x_1691_;
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_a_1692_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1681_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1681_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkUppers_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1670_ = stack[0].m_obj;
lean_object* v_a_1671_ = stack[1].m_obj;
lean_object* v_a_1672_ = stack[2].m_obj;
lean_object* v_a_1673_ = stack[3].m_obj;
lean_object* v_a_1674_ = stack[4].m_obj;
lean_object* v_a_1675_ = stack[5].m_obj;
lean_object* v_a_1676_ = stack[6].m_obj;
lean_object* v_a_1677_ = stack[7].m_obj;
lean_object* v_a_1678_ = stack[8].m_obj;
lean_object* v_a_1679_ = stack[9].m_obj;
lean_object* v_res_1700_;
v_res_1700_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
stack->m_obj
 = v_res_1700_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___boxed(lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec(v_a_1701_);
return v_res_1712_;
}
}
lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(lean_object* v_msg_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_4077__overap_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_obj_once(&l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_4077__overap_1726_ = lean_panic_fn_borrowed(v___x_1725_, v_msg_1713_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
lean_inc(v___y_1715_);
lean_inc(v___y_1714_);
v___x_1727_ = lean_apply_11(v___x_4077__overap_1726_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, lean_box(0));
return v___x_1727_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1713_ = stack[0].m_obj;
lean_object* v___y_1714_ = stack[1].m_obj;
lean_object* v___y_1715_ = stack[2].m_obj;
lean_object* v___y_1716_ = stack[3].m_obj;
lean_object* v___y_1717_ = stack[4].m_obj;
lean_object* v___y_1718_ = stack[5].m_obj;
lean_object* v___y_1719_ = stack[6].m_obj;
lean_object* v___y_1720_ = stack[7].m_obj;
lean_object* v___y_1721_ = stack[8].m_obj;
lean_object* v___y_1722_ = stack[9].m_obj;
lean_object* v___y_1723_ = stack[10].m_obj;
lean_object* v_res_1728_;
v_res_1728_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v_msg_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
stack->m_obj
 = v_res_1728_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___boxed(lean_object* v_msg_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v_msg_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec(v___y_1730_);
return v_res_1741_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_to_int(v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2));
v___x_1747_ = lean_unsigned_to_nat(6u);
v___x_1748_ = lean_unsigned_to_nat(70u);
v___x_1749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_1750_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1751_ = l_mkPanicMessageWithDecl(v___x_1750_, v___x_1749_, v___x_1748_, v___x_1747_, v___x_1746_);
return v___x_1751_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1752_, size_t v_sz_1753_, size_t v_i_1754_, lean_object* v_b_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_usize_dec_lt(v_i_1754_, v_sz_1753_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_b_1755_);
return v___x_1768_;
}
else
{
lean_object* v_snd_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1827_; 
v_snd_1769_ = lean_ctor_get(v_b_1755_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_b_1755_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_b_1755_, 0);
lean_dec(v_unused_1828_);
v___x_1771_ = v_b_1755_;
v_isShared_1772_ = v_isSharedCheck_1827_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snd_1769_);
lean_dec(v_b_1755_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1827_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v_a_1775_; lean_object* v_a_1785_; 
v___x_1773_ = lean_box(0);
v_a_1785_ = lean_array_uget(v_as_1752_, v_i_1754_);
if (lean_obj_tag(v_a_1785_) == 1)
{
lean_object* v_val_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1826_; 
v_val_1786_ = lean_ctor_get(v_a_1785_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_a_1785_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1788_ = v_a_1785_;
v_isShared_1789_ = v_isSharedCheck_1826_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_val_1786_);
lean_dec(v_a_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1826_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_d_1790_; lean_object* v_p_1791_; lean_object* v___x_1792_; 
v_d_1790_ = lean_ctor_get(v_val_1786_, 0);
lean_inc(v_d_1790_);
v_p_1791_ = lean_ctor_get(v_val_1786_, 1);
lean_inc_ref(v_p_1791_);
lean_dec(v_val_1786_);
v___x_1792_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_1791_, v_snd_1769_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec_ref(v_p_1791_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
lean_dec_ref_known(v___x_1792_, 1);
v___x_1793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1794_ = lean_int_dec_lt(v___x_1793_, v_d_1790_);
lean_dec(v_d_1790_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1796_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1795_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1809_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1809_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1809_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
if (lean_obj_tag(v_a_1797_) == 0)
{
lean_object* v___x_1802_; 
lean_del_object(v___x_1771_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v_a_1797_);
v___x_1802_ = v___x_1788_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v_snd_1769_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1803_);
v___x_1805_ = v___x_1799_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
lean_object* v_a_1808_; 
lean_del_object(v___x_1799_);
lean_del_object(v___x_1788_);
lean_dec(v_snd_1769_);
v_a_1808_ = lean_ctor_get(v_a_1797_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v_a_1797_, 1);
v_a_1775_ = v_a_1808_;
goto v___jp_1774_;
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_del_object(v___x_1788_);
lean_del_object(v___x_1771_);
lean_dec(v_snd_1769_);
v_a_1810_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1796_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1796_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_del_object(v___x_1788_);
goto v___jp_1782_;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_d_1790_);
lean_del_object(v___x_1788_);
lean_del_object(v___x_1771_);
lean_dec(v_snd_1769_);
v_a_1818_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1792_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1792_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_dec(v_a_1785_);
goto v___jp_1782_;
}
v___jp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 1, v_a_1775_);
lean_ctor_set(v___x_1771_, 0, v___x_1773_);
v___x_1777_ = v___x_1771_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_a_1775_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
size_t v___x_1778_; size_t v___x_1779_; 
v___x_1778_ = ((size_t)1ULL);
v___x_1779_ = lean_usize_add(v_i_1754_, v___x_1778_);
v_i_1754_ = v___x_1779_;
v_b_1755_ = v___x_1777_;
goto _start;
}
}
v___jp_1782_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(1u);
v___x_1784_ = lean_nat_add(v_snd_1769_, v___x_1783_);
lean_dec(v_snd_1769_);
v_a_1775_ = v___x_1784_;
goto v___jp_1774_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1752_ = stack[0].m_obj;
size_t v_sz_1753_ = stack[1].m_num;
size_t v_i_1754_ = stack[2].m_num;
lean_object* v_b_1755_ = stack[3].m_obj;
lean_object* v___y_1756_ = stack[4].m_obj;
lean_object* v___y_1757_ = stack[5].m_obj;
lean_object* v___y_1758_ = stack[6].m_obj;
lean_object* v___y_1759_ = stack[7].m_obj;
lean_object* v___y_1760_ = stack[8].m_obj;
lean_object* v___y_1761_ = stack[9].m_obj;
lean_object* v___y_1762_ = stack[10].m_obj;
lean_object* v___y_1763_ = stack[11].m_obj;
lean_object* v___y_1764_ = stack[12].m_obj;
lean_object* v___y_1765_ = stack[13].m_obj;
lean_object* v_res_1829_;
v_res_1829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1752_, v_sz_1753_, v_i_1754_, v_b_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
stack->m_obj
 = v_res_1829_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1830_, lean_object* v_sz_1831_, lean_object* v_i_1832_, lean_object* v_b_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
size_t v_sz_boxed_1845_; size_t v_i_boxed_1846_; lean_object* v_res_1847_; 
v_sz_boxed_1845_ = lean_unbox_usize(v_sz_1831_);
lean_dec(v_sz_1831_);
v_i_boxed_1846_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1830_, v_sz_boxed_1845_, v_i_boxed_1846_, v_b_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v_as_1830_);
return v_res_1847_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(lean_object* v_as_1848_, size_t v_sz_1849_, size_t v_i_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_usize_dec_lt(v_i_1850_, v_sz_1849_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_b_1851_);
return v___x_1864_;
}
else
{
lean_object* v_snd_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1923_; 
v_snd_1865_ = lean_ctor_get(v_b_1851_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_b_1851_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v_b_1851_, 0);
lean_dec(v_unused_1924_);
v___x_1867_ = v_b_1851_;
v_isShared_1868_ = v_isSharedCheck_1923_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snd_1865_);
lean_dec(v_b_1851_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1923_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v_a_1871_; lean_object* v_a_1881_; 
v___x_1869_ = lean_box(0);
v_a_1881_ = lean_array_uget(v_as_1848_, v_i_1850_);
if (lean_obj_tag(v_a_1881_) == 1)
{
lean_object* v_val_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1922_; 
v_val_1882_ = lean_ctor_get(v_a_1881_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_a_1881_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1884_ = v_a_1881_;
v_isShared_1885_ = v_isSharedCheck_1922_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_val_1882_);
lean_dec(v_a_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1922_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v_d_1886_; lean_object* v_p_1887_; lean_object* v___x_1888_; 
v_d_1886_ = lean_ctor_get(v_val_1882_, 0);
lean_inc(v_d_1886_);
v_p_1887_ = lean_ctor_get(v_val_1882_, 1);
lean_inc_ref(v_p_1887_);
lean_dec(v_val_1882_);
v___x_1888_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_1887_, v_snd_1865_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec_ref(v_p_1887_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
lean_dec_ref_known(v___x_1888_, 1);
v___x_1889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1890_ = lean_int_dec_lt(v___x_1889_, v_d_1886_);
lean_dec(v_d_1886_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1892_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1891_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1905_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1905_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1905_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
if (lean_obj_tag(v_a_1893_) == 0)
{
lean_object* v___x_1898_; 
lean_del_object(v___x_1867_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v_a_1893_);
v___x_1898_ = v___x_1884_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v_snd_1865_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1899_);
v___x_1901_ = v___x_1895_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; 
lean_del_object(v___x_1895_);
lean_del_object(v___x_1884_);
lean_dec(v_snd_1865_);
v_a_1904_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v_a_1893_, 1);
v_a_1871_ = v_a_1904_;
goto v___jp_1870_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_del_object(v___x_1884_);
lean_del_object(v___x_1867_);
lean_dec(v_snd_1865_);
v_a_1906_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1892_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1892_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_del_object(v___x_1884_);
goto v___jp_1878_;
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_d_1886_);
lean_del_object(v___x_1884_);
lean_del_object(v___x_1867_);
lean_dec(v_snd_1865_);
v_a_1914_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1888_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1888_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
else
{
lean_dec(v_a_1881_);
goto v___jp_1878_;
}
v___jp_1870_:
{
lean_object* v___x_1873_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v_a_1871_);
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1873_ = v___x_1867_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_a_1871_);
v___x_1873_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((size_t)1ULL);
v___x_1875_ = lean_usize_add(v_i_1850_, v___x_1874_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1848_, v_sz_1849_, v___x_1875_, v___x_1873_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1876_;
}
}
v___jp_1878_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_unsigned_to_nat(1u);
v___x_1880_ = lean_nat_add(v_snd_1865_, v___x_1879_);
lean_dec(v_snd_1865_);
v_a_1871_ = v___x_1880_;
goto v___jp_1870_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1848_ = stack[0].m_obj;
size_t v_sz_1849_ = stack[1].m_num;
size_t v_i_1850_ = stack[2].m_num;
lean_object* v_b_1851_ = stack[3].m_obj;
lean_object* v___y_1852_ = stack[4].m_obj;
lean_object* v___y_1853_ = stack[5].m_obj;
lean_object* v___y_1854_ = stack[6].m_obj;
lean_object* v___y_1855_ = stack[7].m_obj;
lean_object* v___y_1856_ = stack[8].m_obj;
lean_object* v___y_1857_ = stack[9].m_obj;
lean_object* v___y_1858_ = stack[10].m_obj;
lean_object* v___y_1859_ = stack[11].m_obj;
lean_object* v___y_1860_ = stack[12].m_obj;
lean_object* v___y_1861_ = stack[13].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_as_1848_, v_sz_1849_, v_i_1850_, v_b_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1926_, lean_object* v_sz_1927_, lean_object* v_i_1928_, lean_object* v_b_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
size_t v_sz_boxed_1941_; size_t v_i_boxed_1942_; lean_object* v_res_1943_; 
v_sz_boxed_1941_ = lean_unbox_usize(v_sz_1927_);
lean_dec(v_sz_1927_);
v_i_boxed_1942_ = lean_unbox_usize(v_i_1928_);
lean_dec(v_i_1928_);
v_res_1943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_as_1926_, v_sz_boxed_1941_, v_i_boxed_1942_, v_b_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v_as_1926_);
return v_res_1943_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(lean_object* v_init_1944_, lean_object* v_n_1945_, lean_object* v_b_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
if (lean_obj_tag(v_n_1945_) == 0)
{
lean_object* v_cs_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; size_t v_sz_1961_; size_t v___x_1962_; lean_object* v___x_1963_; 
v_cs_1958_ = lean_ctor_get(v_n_1945_, 0);
v___x_1959_ = lean_box(0);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v_b_1946_);
v_sz_1961_ = lean_array_size(v_cs_1958_);
v___x_1962_ = ((size_t)0ULL);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_1944_, v_cs_1958_, v_sz_1961_, v___x_1962_, v___x_1960_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1978_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_fst_1968_; 
v_fst_1968_ = lean_ctor_get(v_a_1964_, 0);
if (lean_obj_tag(v_fst_1968_) == 0)
{
lean_object* v_snd_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v_snd_1969_ = lean_ctor_get(v_a_1964_, 1);
lean_inc(v_snd_1969_);
lean_dec(v_a_1964_);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_snd_1969_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1970_);
v___x_1972_ = v___x_1966_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
else
{
lean_object* v_val_1974_; lean_object* v___x_1976_; 
lean_inc_ref(v_fst_1968_);
lean_dec(v_a_1964_);
v_val_1974_ = lean_ctor_get(v_fst_1968_, 0);
lean_inc(v_val_1974_);
lean_dec_ref_known(v_fst_1968_, 1);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_val_1974_);
v___x_1976_ = v___x_1966_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_val_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1963_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1963_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_vs_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; size_t v_sz_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v_vs_1987_ = lean_ctor_get(v_n_1945_, 0);
v___x_1988_ = lean_box(0);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v_b_1946_);
v_sz_1990_ = lean_array_size(v_vs_1987_);
v___x_1991_ = ((size_t)0ULL);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_vs_1987_, v_sz_1990_, v___x_1991_, v___x_1989_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2007_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2007_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2007_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_fst_1997_; 
v_fst_1997_ = lean_ctor_get(v_a_1993_, 0);
if (lean_obj_tag(v_fst_1997_) == 0)
{
lean_object* v_snd_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v_snd_1998_ = lean_ctor_get(v_a_1993_, 1);
lean_inc(v_snd_1998_);
lean_dec(v_a_1993_);
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_snd_1998_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1999_);
v___x_2001_ = v___x_1995_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_object* v_val_2003_; lean_object* v___x_2005_; 
lean_inc_ref(v_fst_1997_);
lean_dec(v_a_1993_);
v_val_2003_ = lean_ctor_get(v_fst_1997_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v_fst_1997_, 1);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v_val_2003_);
v___x_2005_ = v___x_1995_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_val_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_a_2008_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1992_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1992_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1944_ = stack[0].m_obj;
lean_object* v_n_1945_ = stack[1].m_obj;
lean_object* v_b_1946_ = stack[2].m_obj;
lean_object* v___y_1947_ = stack[3].m_obj;
lean_object* v___y_1948_ = stack[4].m_obj;
lean_object* v___y_1949_ = stack[5].m_obj;
lean_object* v___y_1950_ = stack[6].m_obj;
lean_object* v___y_1951_ = stack[7].m_obj;
lean_object* v___y_1952_ = stack[8].m_obj;
lean_object* v___y_1953_ = stack[9].m_obj;
lean_object* v___y_1954_ = stack[10].m_obj;
lean_object* v___y_1955_ = stack[11].m_obj;
lean_object* v___y_1956_ = stack[12].m_obj;
lean_object* v_res_2016_;
v_res_2016_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_1944_, v_n_1945_, v_b_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
stack->m_obj
 = v_res_2016_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(lean_object* v_init_2017_, lean_object* v_as_2018_, size_t v_sz_2019_, size_t v_i_2020_, lean_object* v_b_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_usize_dec_lt(v_i_2020_, v_sz_2019_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_b_2021_);
return v___x_2034_;
}
else
{
lean_object* v_snd_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2069_; 
v_snd_2035_ = lean_ctor_get(v_b_2021_, 1);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_b_2021_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; 
v_unused_2070_ = lean_ctor_get(v_b_2021_, 0);
lean_dec(v_unused_2070_);
v___x_2037_ = v_b_2021_;
v_isShared_2038_ = v_isSharedCheck_2069_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_snd_2035_);
lean_dec(v_b_2021_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2069_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v_a_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_box(0);
v_a_2040_ = lean_array_uget_borrowed(v_as_2018_, v_i_2020_);
lean_inc(v_snd_2035_);
v___x_2041_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2017_, v_a_2040_, v_snd_2035_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2060_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2060_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2060_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
if (lean_obj_tag(v_a_2042_) == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2042_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2046_);
v___x_2048_ = v___x_2037_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_snd_2035_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2048_);
v___x_2050_ = v___x_2044_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; 
lean_del_object(v___x_2044_);
lean_dec(v_snd_2035_);
v_a_2053_ = lean_ctor_get(v_a_2042_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v_a_2042_, 1);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v_a_2053_);
lean_ctor_set(v___x_2037_, 0, v___x_2039_);
v___x_2055_ = v___x_2037_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_a_2053_);
v___x_2055_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
size_t v___x_2056_; size_t v___x_2057_; 
v___x_2056_ = ((size_t)1ULL);
v___x_2057_ = lean_usize_add(v_i_2020_, v___x_2056_);
v_i_2020_ = v___x_2057_;
v_b_2021_ = v___x_2055_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_del_object(v___x_2037_);
lean_dec(v_snd_2035_);
v_a_2061_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2041_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2041_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2017_ = stack[0].m_obj;
lean_object* v_as_2018_ = stack[1].m_obj;
size_t v_sz_2019_ = stack[2].m_num;
size_t v_i_2020_ = stack[3].m_num;
lean_object* v_b_2021_ = stack[4].m_obj;
lean_object* v___y_2022_ = stack[5].m_obj;
lean_object* v___y_2023_ = stack[6].m_obj;
lean_object* v___y_2024_ = stack[7].m_obj;
lean_object* v___y_2025_ = stack[8].m_obj;
lean_object* v___y_2026_ = stack[9].m_obj;
lean_object* v___y_2027_ = stack[10].m_obj;
lean_object* v___y_2028_ = stack[11].m_obj;
lean_object* v___y_2029_ = stack[12].m_obj;
lean_object* v___y_2030_ = stack[13].m_obj;
lean_object* v___y_2031_ = stack[14].m_obj;
lean_object* v_res_2071_;
v_res_2071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_2017_, v_as_2018_, v_sz_2019_, v_i_2020_, v_b_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
stack->m_obj
 = v_res_2071_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2___boxed(lean_object* v_init_2072_, lean_object* v_as_2073_, lean_object* v_sz_2074_, lean_object* v_i_2075_, lean_object* v_b_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
size_t v_sz_boxed_2088_; size_t v_i_boxed_2089_; lean_object* v_res_2090_; 
v_sz_boxed_2088_ = lean_unbox_usize(v_sz_2074_);
lean_dec(v_sz_2074_);
v_i_boxed_2089_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_res_2090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_2072_, v_as_2073_, v_sz_boxed_2088_, v_i_boxed_2089_, v_b_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v_as_2073_);
lean_dec(v_init_2072_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1___boxed(lean_object* v_init_2091_, lean_object* v_n_2092_, lean_object* v_b_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2091_, v_n_2092_, v_b_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v_n_2092_);
lean_dec(v_init_2091_);
return v_res_2105_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(lean_object* v_as_2106_, size_t v_sz_2107_, size_t v_i_2108_, lean_object* v_b_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
uint8_t v___x_2121_; 
v___x_2121_ = lean_usize_dec_lt(v_i_2108_, v_sz_2107_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v_b_2109_);
return v___x_2122_;
}
else
{
lean_object* v_snd_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2182_; 
v_snd_2123_ = lean_ctor_get(v_b_2109_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_b_2109_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; 
v_unused_2183_ = lean_ctor_get(v_b_2109_, 0);
lean_dec(v_unused_2183_);
v___x_2125_ = v_b_2109_;
v_isShared_2126_ = v_isSharedCheck_2182_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_snd_2123_);
lean_dec(v_b_2109_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2182_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v_a_2129_; lean_object* v_a_2139_; 
v___x_2127_ = lean_box(0);
v_a_2139_ = lean_array_uget(v_as_2106_, v_i_2108_);
if (lean_obj_tag(v_a_2139_) == 1)
{
lean_object* v_val_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2181_; 
v_val_2140_ = lean_ctor_get(v_a_2139_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2139_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2142_ = v_a_2139_;
v_isShared_2143_ = v_isSharedCheck_2181_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_val_2140_);
lean_dec(v_a_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2181_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_d_2144_; lean_object* v_p_2145_; lean_object* v___x_2146_; 
v_d_2144_ = lean_ctor_get(v_val_2140_, 0);
lean_inc(v_d_2144_);
v_p_2145_ = lean_ctor_get(v_val_2140_, 1);
lean_inc_ref(v_p_2145_);
lean_dec(v_val_2140_);
v___x_2146_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_2145_, v_snd_2123_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec_ref(v_p_2145_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
lean_dec_ref_known(v___x_2146_, 1);
v___x_2147_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2148_ = lean_int_dec_lt(v___x_2147_, v_d_2144_);
lean_dec(v_d_2144_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2150_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2149_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2164_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2164_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2164_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
if (lean_obj_tag(v_a_2151_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; 
lean_del_object(v___x_2125_);
v_a_2155_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v_a_2151_, 1);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v_a_2155_);
v___x_2157_ = v___x_2142_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2155_);
v___x_2157_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v_snd_2123_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2158_);
v___x_2160_ = v___x_2153_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
else
{
lean_object* v_a_2163_; 
lean_del_object(v___x_2153_);
lean_del_object(v___x_2142_);
lean_dec(v_snd_2123_);
v_a_2163_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v_a_2151_, 1);
v_a_2129_ = v_a_2163_;
goto v___jp_2128_;
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_del_object(v___x_2142_);
lean_del_object(v___x_2125_);
lean_dec(v_snd_2123_);
v_a_2165_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2150_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2150_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_del_object(v___x_2142_);
goto v___jp_2136_;
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_d_2144_);
lean_del_object(v___x_2142_);
lean_del_object(v___x_2125_);
lean_dec(v_snd_2123_);
v_a_2173_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2146_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2146_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
else
{
lean_dec(v_a_2139_);
goto v___jp_2136_;
}
v___jp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 1, v_a_2129_);
lean_ctor_set(v___x_2125_, 0, v___x_2127_);
v___x_2131_ = v___x_2125_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_a_2129_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
size_t v___x_2132_; size_t v___x_2133_; 
v___x_2132_ = ((size_t)1ULL);
v___x_2133_ = lean_usize_add(v_i_2108_, v___x_2132_);
v_i_2108_ = v___x_2133_;
v_b_2109_ = v___x_2131_;
goto _start;
}
}
v___jp_2136_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_add(v_snd_2123_, v___x_2137_);
lean_dec(v_snd_2123_);
v_a_2129_ = v___x_2138_;
goto v___jp_2128_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2106_ = stack[0].m_obj;
size_t v_sz_2107_ = stack[1].m_num;
size_t v_i_2108_ = stack[2].m_num;
lean_object* v_b_2109_ = stack[3].m_obj;
lean_object* v___y_2110_ = stack[4].m_obj;
lean_object* v___y_2111_ = stack[5].m_obj;
lean_object* v___y_2112_ = stack[6].m_obj;
lean_object* v___y_2113_ = stack[7].m_obj;
lean_object* v___y_2114_ = stack[8].m_obj;
lean_object* v___y_2115_ = stack[9].m_obj;
lean_object* v___y_2116_ = stack[10].m_obj;
lean_object* v___y_2117_ = stack[11].m_obj;
lean_object* v___y_2118_ = stack[12].m_obj;
lean_object* v___y_2119_ = stack[13].m_obj;
lean_object* v_res_2184_;
v_res_2184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2106_, v_sz_2107_, v_i_2108_, v_b_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
stack->m_obj
 = v_res_2184_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2185_, lean_object* v_sz_2186_, lean_object* v_i_2187_, lean_object* v_b_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2186_);
lean_dec(v_sz_2186_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2187_);
lean_dec(v_i_2187_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2185_, v_sz_boxed_2200_, v_i_boxed_2201_, v_b_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v_as_2185_);
return v_res_2202_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(lean_object* v_as_2203_, size_t v_sz_2204_, size_t v_i_2205_, lean_object* v_b_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_usize_dec_lt(v_i_2205_, v_sz_2204_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_b_2206_);
return v___x_2219_;
}
else
{
lean_object* v_snd_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2279_; 
v_snd_2220_ = lean_ctor_get(v_b_2206_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_b_2206_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v_b_2206_, 0);
lean_dec(v_unused_2280_);
v___x_2222_ = v_b_2206_;
v_isShared_2223_ = v_isSharedCheck_2279_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_snd_2220_);
lean_dec(v_b_2206_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2279_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v_a_2226_; lean_object* v_a_2236_; 
v___x_2224_ = lean_box(0);
v_a_2236_ = lean_array_uget(v_as_2203_, v_i_2205_);
if (lean_obj_tag(v_a_2236_) == 1)
{
lean_object* v_val_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2278_; 
v_val_2237_ = lean_ctor_get(v_a_2236_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_a_2236_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2239_ = v_a_2236_;
v_isShared_2240_ = v_isSharedCheck_2278_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_val_2237_);
lean_dec(v_a_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2278_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_d_2241_; lean_object* v_p_2242_; lean_object* v___x_2243_; 
v_d_2241_ = lean_ctor_get(v_val_2237_, 0);
lean_inc(v_d_2241_);
v_p_2242_ = lean_ctor_get(v_val_2237_, 1);
lean_inc_ref(v_p_2242_);
lean_dec(v_val_2237_);
v___x_2243_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_2242_, v_snd_2220_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec_ref(v_p_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
lean_dec_ref_known(v___x_2243_, 1);
v___x_2244_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2245_ = lean_int_dec_lt(v___x_2244_, v_d_2241_);
lean_dec(v_d_2241_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2247_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2246_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2261_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2261_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2261_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
if (lean_obj_tag(v_a_2248_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; 
lean_del_object(v___x_2222_);
v_a_2252_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v_a_2248_, 1);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_a_2252_);
v___x_2254_ = v___x_2239_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2252_);
v___x_2254_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v_snd_2220_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2255_);
v___x_2257_ = v___x_2250_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
else
{
lean_object* v_a_2260_; 
lean_del_object(v___x_2250_);
lean_del_object(v___x_2239_);
lean_dec(v_snd_2220_);
v_a_2260_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v_a_2248_, 1);
v_a_2226_ = v_a_2260_;
goto v___jp_2225_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_del_object(v___x_2239_);
lean_del_object(v___x_2222_);
lean_dec(v_snd_2220_);
v_a_2262_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2247_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2247_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_del_object(v___x_2239_);
goto v___jp_2233_;
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_d_2241_);
lean_del_object(v___x_2239_);
lean_del_object(v___x_2222_);
lean_dec(v_snd_2220_);
v_a_2270_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2243_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2243_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
else
{
lean_dec(v_a_2236_);
goto v___jp_2233_;
}
v___jp_2225_:
{
lean_object* v___x_2228_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v_a_2226_);
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2228_ = v___x_2222_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_a_2226_);
v___x_2228_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
size_t v___x_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = ((size_t)1ULL);
v___x_2230_ = lean_usize_add(v_i_2205_, v___x_2229_);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2203_, v_sz_2204_, v___x_2230_, v___x_2228_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
return v___x_2231_;
}
}
v___jp_2233_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_unsigned_to_nat(1u);
v___x_2235_ = lean_nat_add(v_snd_2220_, v___x_2234_);
lean_dec(v_snd_2220_);
v_a_2226_ = v___x_2235_;
goto v___jp_2225_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2203_ = stack[0].m_obj;
size_t v_sz_2204_ = stack[1].m_num;
size_t v_i_2205_ = stack[2].m_num;
lean_object* v_b_2206_ = stack[3].m_obj;
lean_object* v___y_2207_ = stack[4].m_obj;
lean_object* v___y_2208_ = stack[5].m_obj;
lean_object* v___y_2209_ = stack[6].m_obj;
lean_object* v___y_2210_ = stack[7].m_obj;
lean_object* v___y_2211_ = stack[8].m_obj;
lean_object* v___y_2212_ = stack[9].m_obj;
lean_object* v___y_2213_ = stack[10].m_obj;
lean_object* v___y_2214_ = stack[11].m_obj;
lean_object* v___y_2215_ = stack[12].m_obj;
lean_object* v___y_2216_ = stack[13].m_obj;
lean_object* v_res_2281_;
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_as_2203_, v_sz_2204_, v_i_2205_, v_b_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
stack->m_obj
 = v_res_2281_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2___boxed(lean_object* v_as_2282_, lean_object* v_sz_2283_, lean_object* v_i_2284_, lean_object* v_b_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
size_t v_sz_boxed_2297_; size_t v_i_boxed_2298_; lean_object* v_res_2299_; 
v_sz_boxed_2297_ = lean_unbox_usize(v_sz_2283_);
lean_dec(v_sz_2283_);
v_i_boxed_2298_ = lean_unbox_usize(v_i_2284_);
lean_dec(v_i_2284_);
v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_as_2282_, v_sz_boxed_2297_, v_i_boxed_2298_, v_b_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v_as_2282_);
return v_res_2299_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(lean_object* v_t_2300_, lean_object* v_init_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_root_2313_; lean_object* v_tail_2314_; lean_object* v___x_2315_; 
v_root_2313_ = lean_ctor_get(v_t_2300_, 0);
v_tail_2314_ = lean_ctor_get(v_t_2300_, 1);
lean_inc(v_init_2301_);
v___x_2315_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2301_, v_root_2313_, v_init_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v_init_2301_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2352_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2352_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2352_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
if (lean_obj_tag(v_a_2316_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; 
v_a_2320_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v_a_2316_, 1);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_a_2320_);
v___x_2322_ = v___x_2318_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; size_t v_sz_2327_; size_t v___x_2328_; lean_object* v___x_2329_; 
lean_del_object(v___x_2318_);
v_a_2324_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v_a_2316_, 1);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v_a_2324_);
v_sz_2327_ = lean_array_size(v_tail_2314_);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_tail_2314_, v_sz_2327_, v___x_2328_, v___x_2326_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2343_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2343_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2343_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v_fst_2334_; 
v_fst_2334_ = lean_ctor_get(v_a_2330_, 0);
if (lean_obj_tag(v_fst_2334_) == 0)
{
lean_object* v_snd_2335_; lean_object* v___x_2337_; 
v_snd_2335_ = lean_ctor_get(v_a_2330_, 1);
lean_inc(v_snd_2335_);
lean_dec(v_a_2330_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v_snd_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_snd_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
else
{
lean_object* v_val_2339_; lean_object* v___x_2341_; 
lean_inc_ref(v_fst_2334_);
lean_dec(v_a_2330_);
v_val_2339_ = lean_ctor_get(v_fst_2334_, 0);
lean_inc(v_val_2339_);
lean_dec_ref_known(v_fst_2334_, 1);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v_val_2339_);
v___x_2341_ = v___x_2332_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_val_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2329_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2329_);
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
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2315_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2315_);
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
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2300_ = stack[0].m_obj;
lean_object* v_init_2301_ = stack[1].m_obj;
lean_object* v___y_2302_ = stack[2].m_obj;
lean_object* v___y_2303_ = stack[3].m_obj;
lean_object* v___y_2304_ = stack[4].m_obj;
lean_object* v___y_2305_ = stack[5].m_obj;
lean_object* v___y_2306_ = stack[6].m_obj;
lean_object* v___y_2307_ = stack[7].m_obj;
lean_object* v___y_2308_ = stack[8].m_obj;
lean_object* v___y_2309_ = stack[9].m_obj;
lean_object* v___y_2310_ = stack[10].m_obj;
lean_object* v___y_2311_ = stack[11].m_obj;
lean_object* v_res_2361_;
v_res_2361_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_t_2300_, v_init_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
stack->m_obj
 = v_res_2361_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1___boxed(lean_object* v_t_2362_, lean_object* v_init_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_t_2362_, v_init_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v_t_2362_);
return v_res_2375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2377_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0));
v___x_2378_ = lean_unsigned_to_nat(2u);
v___x_2379_ = lean_unsigned_to_nat(65u);
v___x_2380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_2381_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2382_ = l_mkPanicMessageWithDecl(v___x_2381_, v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_);
return v___x_2382_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2383_, v_a_2391_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v_vars_2396_; lean_object* v_dvds_2397_; lean_object* v_size_2398_; lean_object* v_size_2399_; uint8_t v___x_2400_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v_vars_2396_ = lean_ctor_get(v_a_2395_, 0);
lean_inc_ref(v_vars_2396_);
v_dvds_2397_ = lean_ctor_get(v_a_2395_, 5);
lean_inc_ref(v_dvds_2397_);
lean_dec(v_a_2395_);
v_size_2398_ = lean_ctor_get(v_vars_2396_, 2);
lean_inc(v_size_2398_);
lean_dec_ref(v_vars_2396_);
v_size_2399_ = lean_ctor_get(v_dvds_2397_, 2);
v___x_2400_ = lean_nat_dec_eq(v_size_2398_, v_size_2399_);
lean_dec(v_size_2398_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec_ref(v_dvds_2397_);
v___x_2401_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1);
v___x_2402_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2401_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2402_;
}
else
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_dvds_2397_, v___x_2403_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec_ref(v_dvds_2397_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2412_; 
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; 
v_unused_2413_ = lean_ctor_get(v___x_2404_, 0);
lean_dec(v_unused_2413_);
v___x_2406_ = v___x_2404_;
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
else
{
lean_dec(v___x_2404_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = lean_box(0);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2408_);
v___x_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
v_a_2414_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2404_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2404_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_a_2422_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2394_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2394_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkDvds_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2383_ = stack[0].m_obj;
lean_object* v_a_2384_ = stack[1].m_obj;
lean_object* v_a_2385_ = stack[2].m_obj;
lean_object* v_a_2386_ = stack[3].m_obj;
lean_object* v_a_2387_ = stack[4].m_obj;
lean_object* v_a_2388_ = stack[5].m_obj;
lean_object* v_a_2389_ = stack[6].m_obj;
lean_object* v_a_2390_ = stack[7].m_obj;
lean_object* v_a_2391_ = stack[8].m_obj;
lean_object* v_a_2392_ = stack[9].m_obj;
lean_object* v_res_2430_;
v_res_2430_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
stack->m_obj
 = v_res_2430_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___boxed(lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec(v_a_2431_);
return v_res_2442_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2444_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_2445_ = lean_unsigned_to_nat(6u);
v___x_2446_ = lean_unsigned_to_nat(81u);
v___x_2447_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2448_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2449_ = l_mkPanicMessageWithDecl(v___x_2448_, v___x_2447_, v___x_2446_, v___x_2445_, v___x_2444_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2451_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2));
v___x_2452_ = lean_unsigned_to_nat(6u);
v___x_2453_ = lean_unsigned_to_nat(79u);
v___x_2454_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2455_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2456_ = l_mkPanicMessageWithDecl(v___x_2455_, v___x_2454_, v___x_2453_, v___x_2452_, v___x_2451_);
return v___x_2456_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(lean_object* v_vars_2457_, lean_object* v___x_2458_, lean_object* v_x_2459_, lean_object* v_____s_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v_size_2479_; uint8_t v___x_2480_; 
v_fst_2477_ = lean_ctor_get(v_x_2459_, 0);
v_snd_2478_ = lean_ctor_get(v_x_2459_, 1);
v_size_2479_ = lean_ctor_get(v_vars_2457_, 2);
v___x_2480_ = lean_nat_dec_lt(v_snd_2478_, v_size_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1);
v___x_2482_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2481_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_dec_ref_known(v___x_2482_, 1);
goto v___jp_2472_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; uint8_t v___x_2494_; 
v___x_2491_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2458_, v_vars_2457_, v_snd_2478_);
v___x_2492_ = lean_ptr_addr(v_fst_2477_);
v___x_2493_ = lean_ptr_addr(v___x_2491_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_usize_dec_eq(v___x_2492_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3);
v___x_2496_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2495_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v___x_2496_;
}
else
{
goto v___jp_2472_;
}
}
v___jp_2472_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2473_ = lean_unsigned_to_nat(1u);
v___x_2474_ = lean_nat_add(v_____s_2460_, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_vars_2457_ = stack[0].m_obj;
lean_object* v___x_2458_ = stack[1].m_obj;
lean_object* v_x_2459_ = stack[2].m_obj;
lean_object* v_____s_2460_ = stack[3].m_obj;
lean_object* v___y_2461_ = stack[4].m_obj;
lean_object* v___y_2462_ = stack[5].m_obj;
lean_object* v___y_2463_ = stack[6].m_obj;
lean_object* v___y_2464_ = stack[7].m_obj;
lean_object* v___y_2465_ = stack[8].m_obj;
lean_object* v___y_2466_ = stack[9].m_obj;
lean_object* v___y_2467_ = stack[10].m_obj;
lean_object* v___y_2468_ = stack[11].m_obj;
lean_object* v___y_2469_ = stack[12].m_obj;
lean_object* v___y_2470_ = stack[13].m_obj;
lean_object* v_res_2497_;
v_res_2497_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(v_vars_2457_, v___x_2458_, v_x_2459_, v_____s_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
stack->m_obj
 = v_res_2497_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(lean_object* v_vars_2498_, lean_object* v___x_2499_, lean_object* v_x_2500_, lean_object* v_____s_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(v_vars_2498_, v___x_2499_, v_x_2500_, v_____s_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec(v_____s_2501_);
lean_dec_ref(v_x_2500_);
lean_dec_ref(v___x_2499_);
lean_dec_ref(v_vars_2498_);
return v_res_2513_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2514_, lean_object* v_keys_2515_, lean_object* v_vals_2516_, lean_object* v_i_2517_, lean_object* v_acc_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = lean_array_get_size(v_keys_2515_);
v___x_2531_ = lean_nat_dec_lt(v_i_2517_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_dec(v_i_2517_);
lean_dec_ref(v_f_2514_);
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_acc_2518_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
return v___x_2533_;
}
else
{
lean_object* v_k_2534_; lean_object* v_v_2535_; lean_object* v___x_2536_; 
v_k_2534_ = lean_array_fget_borrowed(v_keys_2515_, v_i_2517_);
v_v_2535_ = lean_array_fget_borrowed(v_vals_2516_, v_i_2517_);
lean_inc_ref(v_f_2514_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc(v_v_2535_);
lean_inc(v_k_2534_);
v___x_2536_ = lean_apply_14(v_f_2514_, v_acc_2518_, v_k_2534_, v_v_2535_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, lean_box(0));
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
if (lean_obj_tag(v_a_2537_) == 0)
{
lean_dec_ref_known(v_a_2537_, 1);
lean_dec(v_i_2517_);
lean_dec_ref(v_f_2514_);
return v___x_2536_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_dec_ref_known(v___x_2536_, 1);
v_a_2538_ = lean_ctor_get(v_a_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v_a_2537_, 1);
v___x_2539_ = lean_unsigned_to_nat(1u);
v___x_2540_ = lean_nat_add(v_i_2517_, v___x_2539_);
lean_dec(v_i_2517_);
v_i_2517_ = v___x_2540_;
v_acc_2518_ = v_a_2538_;
goto _start;
}
}
else
{
lean_dec(v_i_2517_);
lean_dec_ref(v_f_2514_);
return v___x_2536_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2514_ = stack[0].m_obj;
lean_object* v_keys_2515_ = stack[1].m_obj;
lean_object* v_vals_2516_ = stack[2].m_obj;
lean_object* v_i_2517_ = stack[3].m_obj;
lean_object* v_acc_2518_ = stack[4].m_obj;
lean_object* v___y_2519_ = stack[5].m_obj;
lean_object* v___y_2520_ = stack[6].m_obj;
lean_object* v___y_2521_ = stack[7].m_obj;
lean_object* v___y_2522_ = stack[8].m_obj;
lean_object* v___y_2523_ = stack[9].m_obj;
lean_object* v___y_2524_ = stack[10].m_obj;
lean_object* v___y_2525_ = stack[11].m_obj;
lean_object* v___y_2526_ = stack[12].m_obj;
lean_object* v___y_2527_ = stack[13].m_obj;
lean_object* v___y_2528_ = stack[14].m_obj;
lean_object* v_res_2542_;
v_res_2542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2514_, v_keys_2515_, v_vals_2516_, v_i_2517_, v_acc_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
stack->m_obj
 = v_res_2542_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2543_, lean_object* v_keys_2544_, lean_object* v_vals_2545_, lean_object* v_i_2546_, lean_object* v_acc_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2543_, v_keys_2544_, v_vals_2545_, v_i_2546_, v_acc_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v_vals_2545_);
lean_dec_ref(v_keys_2544_);
return v_res_2559_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2560_, lean_object* v_as_2561_, size_t v_i_2562_, size_t v_stop_2563_, lean_object* v_b_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_a_2577_; lean_object* v___y_2582_; uint8_t v___x_2585_; 
v___x_2585_ = lean_usize_dec_eq(v_i_2562_, v_stop_2563_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_array_uget_borrowed(v_as_2561_, v_i_2562_);
switch(lean_obj_tag(v___x_2586_))
{
case 0:
{
lean_object* v_key_2587_; lean_object* v_val_2588_; lean_object* v___x_2589_; 
v_key_2587_ = lean_ctor_get(v___x_2586_, 0);
v_val_2588_ = lean_ctor_get(v___x_2586_, 1);
lean_inc_ref(v_f_2560_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc(v___y_2568_);
lean_inc_ref(v___y_2567_);
lean_inc(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc(v_val_2588_);
lean_inc(v_key_2587_);
v___x_2589_ = lean_apply_14(v_f_2560_, v_b_2564_, v_key_2587_, v_val_2588_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, lean_box(0));
v___y_2582_ = v___x_2589_;
goto v___jp_2581_;
}
case 1:
{
lean_object* v_node_2590_; lean_object* v___x_2591_; 
v_node_2590_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_node_2590_);
lean_inc_ref(v_f_2560_);
v___x_2591_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2560_, v_node_2590_, v_b_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
v___y_2582_ = v___x_2591_;
goto v___jp_2581_;
}
default: 
{
v_a_2577_ = v_b_2564_;
goto v___jp_2576_;
}
}
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref(v_f_2560_);
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v_b_2564_);
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
return v___x_2593_;
}
v___jp_2576_:
{
size_t v___x_2578_; size_t v___x_2579_; 
v___x_2578_ = ((size_t)1ULL);
v___x_2579_ = lean_usize_add(v_i_2562_, v___x_2578_);
v_i_2562_ = v___x_2579_;
v_b_2564_ = v_a_2577_;
goto _start;
}
v___jp_2581_:
{
if (lean_obj_tag(v___y_2582_) == 0)
{
lean_object* v_a_2583_; 
v_a_2583_ = lean_ctor_get(v___y_2582_, 0);
if (lean_obj_tag(v_a_2583_) == 0)
{
lean_dec_ref(v_f_2560_);
return v___y_2582_;
}
else
{
lean_object* v_a_2584_; 
lean_inc_ref(v_a_2583_);
lean_dec_ref_known(v___y_2582_, 1);
v_a_2584_ = lean_ctor_get(v_a_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v_a_2583_, 1);
v_a_2577_ = v_a_2584_;
goto v___jp_2576_;
}
}
else
{
lean_dec_ref(v_f_2560_);
return v___y_2582_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2560_ = stack[0].m_obj;
lean_object* v_as_2561_ = stack[1].m_obj;
size_t v_i_2562_ = stack[2].m_num;
size_t v_stop_2563_ = stack[3].m_num;
lean_object* v_b_2564_ = stack[4].m_obj;
lean_object* v___y_2565_ = stack[5].m_obj;
lean_object* v___y_2566_ = stack[6].m_obj;
lean_object* v___y_2567_ = stack[7].m_obj;
lean_object* v___y_2568_ = stack[8].m_obj;
lean_object* v___y_2569_ = stack[9].m_obj;
lean_object* v___y_2570_ = stack[10].m_obj;
lean_object* v___y_2571_ = stack[11].m_obj;
lean_object* v___y_2572_ = stack[12].m_obj;
lean_object* v___y_2573_ = stack[13].m_obj;
lean_object* v___y_2574_ = stack[14].m_obj;
lean_object* v_res_2594_;
v_res_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2560_, v_as_2561_, v_i_2562_, v_stop_2563_, v_b_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
stack->m_obj
 = v_res_2594_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
if (lean_obj_tag(v_x_2596_) == 0)
{
lean_object* v_es_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2623_; 
v_es_2609_ = lean_ctor_get(v_x_2596_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_x_2596_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2611_ = v_x_2596_;
v_isShared_2612_ = v_isSharedCheck_2623_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_es_2609_);
lean_dec(v_x_2596_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2623_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_array_get_size(v_es_2609_);
v___x_2615_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2617_; 
lean_dec_ref(v_es_2609_);
lean_dec_ref(v_f_2595_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 0, v_x_2597_);
v___x_2617_ = v___x_2611_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_x_2597_);
v___x_2617_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
}
else
{
size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
lean_del_object(v___x_2611_);
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = lean_usize_of_nat(v___x_2614_);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2595_, v_es_2609_, v___x_2620_, v___x_2621_, v_x_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_es_2609_);
return v___x_2622_;
}
}
}
else
{
lean_object* v_ks_2624_; lean_object* v_vs_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_ks_2624_ = lean_ctor_get(v_x_2596_, 0);
lean_inc_ref(v_ks_2624_);
v_vs_2625_ = lean_ctor_get(v_x_2596_, 1);
lean_inc_ref(v_vs_2625_);
lean_dec_ref_known(v_x_2596_, 2);
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2595_, v_ks_2624_, v_vs_2625_, v___x_2626_, v_x_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_vs_2625_);
lean_dec_ref(v_ks_2624_);
return v___x_2627_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2595_ = stack[0].m_obj;
lean_object* v_x_2596_ = stack[1].m_obj;
lean_object* v_x_2597_ = stack[2].m_obj;
lean_object* v___y_2598_ = stack[3].m_obj;
lean_object* v___y_2599_ = stack[4].m_obj;
lean_object* v___y_2600_ = stack[5].m_obj;
lean_object* v___y_2601_ = stack[6].m_obj;
lean_object* v___y_2602_ = stack[7].m_obj;
lean_object* v___y_2603_ = stack[8].m_obj;
lean_object* v___y_2604_ = stack[9].m_obj;
lean_object* v___y_2605_ = stack[10].m_obj;
lean_object* v___y_2606_ = stack[11].m_obj;
lean_object* v___y_2607_ = stack[12].m_obj;
lean_object* v_res_2628_;
v_res_2628_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2595_, v_x_2596_, v_x_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
stack->m_obj
 = v_res_2628_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2629_, v_x_2630_, v_x_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec(v___y_2632_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2644_, lean_object* v_as_2645_, lean_object* v_i_2646_, lean_object* v_stop_2647_, lean_object* v_b_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
size_t v_i_boxed_2660_; size_t v_stop_boxed_2661_; lean_object* v_res_2662_; 
v_i_boxed_2660_ = lean_unbox_usize(v_i_2646_);
lean_dec(v_i_2646_);
v_stop_boxed_2661_ = lean_unbox_usize(v_stop_2647_);
lean_dec(v_stop_2647_);
v_res_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2644_, v_as_2645_, v_i_boxed_2660_, v_stop_boxed_2661_, v_b_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v_as_2645_);
return v_res_2662_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(lean_object* v_f_2663_, lean_object* v_s_2664_, lean_object* v_a_2665_, lean_object* v_b_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_a_2665_);
lean_ctor_set(v___x_2678_, 1, v_b_2666_);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v___y_2674_);
lean_inc_ref(v___y_2673_);
lean_inc(v___y_2672_);
lean_inc_ref(v___y_2671_);
lean_inc(v___y_2670_);
lean_inc_ref(v___y_2669_);
lean_inc(v___y_2668_);
lean_inc(v___y_2667_);
v___x_2679_ = lean_apply_13(v_f_2663_, v___x_2678_, v_s_2664_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, lean_box(0));
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2706_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2706_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2706_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
if (lean_obj_tag(v_a_2680_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2694_; 
v_a_2684_ = lean_ctor_get(v_a_2680_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2680_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2686_ = v_a_2680_;
v_isShared_2687_ = v_isSharedCheck_2694_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v_a_2680_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2694_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2691_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2689_);
v___x_2691_ = v___x_2682_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2705_; 
v_a_2695_ = lean_ctor_get(v_a_2680_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_a_2680_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2697_ = v_a_2680_;
v_isShared_2698_ = v_isSharedCheck_2705_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v_a_2680_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2705_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2700_);
v___x_2702_ = v___x_2682_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
v_a_2707_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2679_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2679_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2663_ = stack[0].m_obj;
lean_object* v_s_2664_ = stack[1].m_obj;
lean_object* v_a_2665_ = stack[2].m_obj;
lean_object* v_b_2666_ = stack[3].m_obj;
lean_object* v___y_2667_ = stack[4].m_obj;
lean_object* v___y_2668_ = stack[5].m_obj;
lean_object* v___y_2669_ = stack[6].m_obj;
lean_object* v___y_2670_ = stack[7].m_obj;
lean_object* v___y_2671_ = stack[8].m_obj;
lean_object* v___y_2672_ = stack[9].m_obj;
lean_object* v___y_2673_ = stack[10].m_obj;
lean_object* v___y_2674_ = stack[11].m_obj;
lean_object* v___y_2675_ = stack[12].m_obj;
lean_object* v___y_2676_ = stack[13].m_obj;
lean_object* v_res_2715_;
v_res_2715_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(v_f_2663_, v_s_2664_, v_a_2665_, v_b_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
stack->m_obj
 = v_res_2715_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed(lean_object* v_f_2716_, lean_object* v_s_2717_, lean_object* v_a_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(v_f_2716_, v_s_2717_, v_a_2718_, v_b_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec(v___y_2720_);
return v_res_2731_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(lean_object* v_map_2732_, lean_object* v_init_2733_, lean_object* v_f_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___f_2746_; lean_object* v___x_2747_; 
v___f_2746_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed), 15, 1);
lean_closure_set(v___f_2746_, 0, v_f_2734_);
lean_inc_ref(v_map_2732_);
v___x_2747_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v___f_2746_, v_map_2732_, v_init_2733_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2756_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2756_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2756_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_a_2752_; lean_object* v___x_2754_; 
v_a_2752_ = lean_ctor_get(v_a_2748_, 0);
lean_inc(v_a_2752_);
lean_dec(v_a_2748_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v_a_2752_);
v___x_2754_ = v___x_2750_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2747_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2747_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_2732_ = stack[0].m_obj;
lean_object* v_init_2733_ = stack[1].m_obj;
lean_object* v_f_2734_ = stack[2].m_obj;
lean_object* v___y_2735_ = stack[3].m_obj;
lean_object* v___y_2736_ = stack[4].m_obj;
lean_object* v___y_2737_ = stack[5].m_obj;
lean_object* v___y_2738_ = stack[6].m_obj;
lean_object* v___y_2739_ = stack[7].m_obj;
lean_object* v___y_2740_ = stack[8].m_obj;
lean_object* v___y_2741_ = stack[9].m_obj;
lean_object* v___y_2742_ = stack[10].m_obj;
lean_object* v___y_2743_ = stack[11].m_obj;
lean_object* v___y_2744_ = stack[12].m_obj;
lean_object* v_res_2765_;
v_res_2765_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2732_, v_init_2733_, v_f_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
stack->m_obj
 = v_res_2765_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___boxed(lean_object* v_map_2766_, lean_object* v_init_2767_, lean_object* v_f_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2766_, v_init_2767_, v_f_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v_map_2766_);
return v_res_2780_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2782_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0));
v___x_2783_ = lean_unsigned_to_nat(2u);
v___x_2784_ = lean_unsigned_to_nat(83u);
v___x_2785_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2786_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2787_ = l_mkPanicMessageWithDecl(v___x_2786_, v___x_2785_, v___x_2784_, v___x_2783_, v___x_2782_);
return v___x_2787_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars(lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = l_Lean_instInhabitedExpr;
v___x_2800_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2788_, v_a_2796_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v_vars_2802_; lean_object* v_varMap_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v_vars_2802_ = lean_ctor_get(v_a_2801_, 0);
lean_inc_ref_n(v_vars_2802_, 2);
v_varMap_2803_ = lean_ctor_get(v_a_2801_, 1);
lean_inc_ref(v_varMap_2803_);
lean_dec(v_a_2801_);
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2804_, 0, v_vars_2802_);
lean_closure_set(v___f_2804_, 1, v___x_2799_);
v___x_2805_ = lean_unsigned_to_nat(0u);
v___x_2806_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_varMap_2803_, v___x_2805_, v___f_2804_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec_ref(v_varMap_2803_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2819_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2819_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2819_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v_size_2811_; uint8_t v___x_2812_; 
v_size_2811_ = lean_ctor_get(v_vars_2802_, 2);
lean_inc(v_size_2811_);
lean_dec_ref(v_vars_2802_);
v___x_2812_ = lean_nat_dec_eq(v_size_2811_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec(v_size_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_del_object(v___x_2809_);
v___x_2813_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1);
v___x_2814_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2813_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = lean_box(0);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2815_);
v___x_2817_ = v___x_2809_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_vars_2802_);
v_a_2820_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2806_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2806_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v_a_2828_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2800_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2800_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2788_ = stack[0].m_obj;
lean_object* v_a_2789_ = stack[1].m_obj;
lean_object* v_a_2790_ = stack[2].m_obj;
lean_object* v_a_2791_ = stack[3].m_obj;
lean_object* v_a_2792_ = stack[4].m_obj;
lean_object* v_a_2793_ = stack[5].m_obj;
lean_object* v_a_2794_ = stack[6].m_obj;
lean_object* v_a_2795_ = stack[7].m_obj;
lean_object* v_a_2796_ = stack[8].m_obj;
lean_object* v_a_2797_ = stack[9].m_obj;
lean_object* v_res_2836_;
v_res_2836_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
stack->m_obj
 = v_res_2836_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___boxed(lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec(v_a_2837_);
return v_res_2848_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(lean_object* v_00_u03c3_2849_, lean_object* v_00_u03b2_2850_, lean_object* v_map_2851_, lean_object* v_init_2852_, lean_object* v_f_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2851_, v_init_2852_, v_f_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_2851_ = stack[2].m_obj;
lean_object* v_init_2852_ = stack[3].m_obj;
lean_object* v_f_2853_ = stack[4].m_obj;
lean_object* v___y_2854_ = stack[5].m_obj;
lean_object* v___y_2855_ = stack[6].m_obj;
lean_object* v___y_2856_ = stack[7].m_obj;
lean_object* v___y_2857_ = stack[8].m_obj;
lean_object* v___y_2858_ = stack[9].m_obj;
lean_object* v___y_2859_ = stack[10].m_obj;
lean_object* v___y_2860_ = stack[11].m_obj;
lean_object* v___y_2861_ = stack[12].m_obj;
lean_object* v___y_2862_ = stack[13].m_obj;
lean_object* v___y_2863_ = stack[14].m_obj;
lean_object* v_res_2866_;
v_res_2866_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(lean_box(0), lean_box(0), v_map_2851_, v_init_2852_, v_f_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
stack->m_obj
 = v_res_2866_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___boxed(lean_object* v_00_u03c3_2867_, lean_object* v_00_u03b2_2868_, lean_object* v_map_2869_, lean_object* v_init_2870_, lean_object* v_f_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(v_00_u03c3_2867_, v_00_u03b2_2868_, v_map_2869_, v_init_2870_, v_f_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v_map_2869_);
return v_res_2883_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(lean_object* v_map_2884_, lean_object* v_f_2885_, lean_object* v_init_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2885_, v_map_2884_, v_init_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_2884_ = stack[0].m_obj;
lean_object* v_f_2885_ = stack[1].m_obj;
lean_object* v_init_2886_ = stack[2].m_obj;
lean_object* v___y_2887_ = stack[3].m_obj;
lean_object* v___y_2888_ = stack[4].m_obj;
lean_object* v___y_2889_ = stack[5].m_obj;
lean_object* v___y_2890_ = stack[6].m_obj;
lean_object* v___y_2891_ = stack[7].m_obj;
lean_object* v___y_2892_ = stack[8].m_obj;
lean_object* v___y_2893_ = stack[9].m_obj;
lean_object* v___y_2894_ = stack[10].m_obj;
lean_object* v___y_2895_ = stack[11].m_obj;
lean_object* v___y_2896_ = stack[12].m_obj;
lean_object* v_res_2899_;
v_res_2899_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(v_map_2884_, v_f_2885_, v_init_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
stack->m_obj
 = v_res_2899_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_map_2900_, lean_object* v_f_2901_, lean_object* v_init_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(v_map_2900_, v_f_2901_, v_init_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec(v___y_2903_);
return v_res_2914_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(lean_object* v_00_u03c3_2915_, lean_object* v_00_u03c3_2916_, lean_object* v_00_u03b2_2917_, lean_object* v_map_2918_, lean_object* v_f_2919_, lean_object* v_init_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2919_, v_map_2918_, v_init_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
return v___x_2932_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_2918_ = stack[3].m_obj;
lean_object* v_f_2919_ = stack[4].m_obj;
lean_object* v_init_2920_ = stack[5].m_obj;
lean_object* v___y_2921_ = stack[6].m_obj;
lean_object* v___y_2922_ = stack[7].m_obj;
lean_object* v___y_2923_ = stack[8].m_obj;
lean_object* v___y_2924_ = stack[9].m_obj;
lean_object* v___y_2925_ = stack[10].m_obj;
lean_object* v___y_2926_ = stack[11].m_obj;
lean_object* v___y_2927_ = stack[12].m_obj;
lean_object* v___y_2928_ = stack[13].m_obj;
lean_object* v___y_2929_ = stack[14].m_obj;
lean_object* v___y_2930_ = stack[15].m_obj;
lean_object* v_res_2933_;
v_res_2933_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(lean_box(0), lean_box(0), lean_box(0), v_map_2918_, v_f_2919_, v_init_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
stack->m_obj
 = v_res_2933_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_2934_ = _args[0];
lean_object* v_00_u03c3_2935_ = _args[1];
lean_object* v_00_u03b2_2936_ = _args[2];
lean_object* v_map_2937_ = _args[3];
lean_object* v_f_2938_ = _args[4];
lean_object* v_init_2939_ = _args[5];
lean_object* v___y_2940_ = _args[6];
lean_object* v___y_2941_ = _args[7];
lean_object* v___y_2942_ = _args[8];
lean_object* v___y_2943_ = _args[9];
lean_object* v___y_2944_ = _args[10];
lean_object* v___y_2945_ = _args[11];
lean_object* v___y_2946_ = _args[12];
lean_object* v___y_2947_ = _args[13];
lean_object* v___y_2948_ = _args[14];
lean_object* v___y_2949_ = _args[15];
lean_object* v___y_2950_ = _args[16];
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(v_00_u03c3_2934_, v_00_u03c3_2935_, v_00_u03b2_2936_, v_map_2937_, v_f_2938_, v_init_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
return v_res_2951_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2952_, lean_object* v_00_u03c3_2953_, lean_object* v_00_u03b1_2954_, lean_object* v_00_u03b2_2955_, lean_object* v_f_2956_, lean_object* v_x_2957_, lean_object* v_x_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2956_, v_x_2957_, v_x_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2956_ = stack[4].m_obj;
lean_object* v_x_2957_ = stack[5].m_obj;
lean_object* v_x_2958_ = stack[6].m_obj;
lean_object* v___y_2959_ = stack[7].m_obj;
lean_object* v___y_2960_ = stack[8].m_obj;
lean_object* v___y_2961_ = stack[9].m_obj;
lean_object* v___y_2962_ = stack[10].m_obj;
lean_object* v___y_2963_ = stack[11].m_obj;
lean_object* v___y_2964_ = stack[12].m_obj;
lean_object* v___y_2965_ = stack[13].m_obj;
lean_object* v___y_2966_ = stack[14].m_obj;
lean_object* v___y_2967_ = stack[15].m_obj;
lean_object* v___y_2968_ = stack[16].m_obj;
lean_object* v_res_2971_;
v_res_2971_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_2956_, v_x_2957_, v_x_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
stack->m_obj
 = v_res_2971_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2991_, lean_object* v_00_u03b2_2992_, lean_object* v_00_u03c3_2993_, lean_object* v_00_u03c3_2994_, lean_object* v_f_2995_, lean_object* v_as_2996_, size_t v_i_2997_, size_t v_stop_2998_, lean_object* v_b_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2995_, v_as_2996_, v_i_2997_, v_stop_2998_, v_b_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2995_ = stack[4].m_obj;
lean_object* v_as_2996_ = stack[5].m_obj;
size_t v_i_2997_ = stack[6].m_num;
size_t v_stop_2998_ = stack[7].m_num;
lean_object* v_b_2999_ = stack[8].m_obj;
lean_object* v___y_3000_ = stack[9].m_obj;
lean_object* v___y_3001_ = stack[10].m_obj;
lean_object* v___y_3002_ = stack[11].m_obj;
lean_object* v___y_3003_ = stack[12].m_obj;
lean_object* v___y_3004_ = stack[13].m_obj;
lean_object* v___y_3005_ = stack[14].m_obj;
lean_object* v___y_3006_ = stack[15].m_obj;
lean_object* v___y_3007_ = stack[16].m_obj;
lean_object* v___y_3008_ = stack[17].m_obj;
lean_object* v___y_3009_ = stack[18].m_obj;
lean_object* v_res_3012_;
v_res_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_2995_, v_as_2996_, v_i_2997_, v_stop_2998_, v_b_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
stack->m_obj
 = v_res_3012_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03b1_3013_ = _args[0];
lean_object* v_00_u03b2_3014_ = _args[1];
lean_object* v_00_u03c3_3015_ = _args[2];
lean_object* v_00_u03c3_3016_ = _args[3];
lean_object* v_f_3017_ = _args[4];
lean_object* v_as_3018_ = _args[5];
lean_object* v_i_3019_ = _args[6];
lean_object* v_stop_3020_ = _args[7];
lean_object* v_b_3021_ = _args[8];
lean_object* v___y_3022_ = _args[9];
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
_start:
{
size_t v_i_boxed_3033_; size_t v_stop_boxed_3034_; lean_object* v_res_3035_; 
v_i_boxed_3033_ = lean_unbox_usize(v_i_3019_);
lean_dec(v_i_3019_);
v_stop_boxed_3034_ = lean_unbox_usize(v_stop_3020_);
lean_dec(v_stop_3020_);
v_res_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3013_, v_00_u03b2_3014_, v_00_u03c3_3015_, v_00_u03c3_3016_, v_f_3017_, v_as_3018_, v_i_boxed_3033_, v_stop_boxed_3034_, v_b_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v_as_3018_);
return v_res_3035_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3036_, lean_object* v_00_u03c3_3037_, lean_object* v_00_u03b1_3038_, lean_object* v_00_u03b2_3039_, lean_object* v_f_3040_, lean_object* v_keys_3041_, lean_object* v_vals_3042_, lean_object* v_heq_3043_, lean_object* v_i_3044_, lean_object* v_acc_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3040_, v_keys_3041_, v_vals_3042_, v_i_3044_, v_acc_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
return v___x_3057_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3040_ = stack[4].m_obj;
lean_object* v_keys_3041_ = stack[5].m_obj;
lean_object* v_vals_3042_ = stack[6].m_obj;
lean_object* v_i_3044_ = stack[8].m_obj;
lean_object* v_acc_3045_ = stack[9].m_obj;
lean_object* v___y_3046_ = stack[10].m_obj;
lean_object* v___y_3047_ = stack[11].m_obj;
lean_object* v___y_3048_ = stack[12].m_obj;
lean_object* v___y_3049_ = stack[13].m_obj;
lean_object* v___y_3050_ = stack[14].m_obj;
lean_object* v___y_3051_ = stack[15].m_obj;
lean_object* v___y_3052_ = stack[16].m_obj;
lean_object* v___y_3053_ = stack[17].m_obj;
lean_object* v___y_3054_ = stack[18].m_obj;
lean_object* v___y_3055_ = stack[19].m_obj;
lean_object* v_res_3058_;
v_res_3058_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_3040_, v_keys_3041_, v_vals_3042_, lean_box(0), v_i_3044_, v_acc_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
stack->m_obj
 = v_res_3058_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_3059_ = _args[0];
lean_object* v_00_u03c3_3060_ = _args[1];
lean_object* v_00_u03b1_3061_ = _args[2];
lean_object* v_00_u03b2_3062_ = _args[3];
lean_object* v_f_3063_ = _args[4];
lean_object* v_keys_3064_ = _args[5];
lean_object* v_vals_3065_ = _args[6];
lean_object* v_heq_3066_ = _args[7];
lean_object* v_i_3067_ = _args[8];
lean_object* v_acc_3068_ = _args[9];
lean_object* v___y_3069_ = _args[10];
lean_object* v___y_3070_ = _args[11];
lean_object* v___y_3071_ = _args[12];
lean_object* v___y_3072_ = _args[13];
lean_object* v___y_3073_ = _args[14];
lean_object* v___y_3074_ = _args[15];
lean_object* v___y_3075_ = _args[16];
lean_object* v___y_3076_ = _args[17];
lean_object* v___y_3077_ = _args[18];
lean_object* v___y_3078_ = _args[19];
lean_object* v___y_3079_ = _args[20];
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3059_, v_00_u03c3_3060_, v_00_u03b1_3061_, v_00_u03b2_3062_, v_f_3063_, v_keys_3064_, v_vals_3065_, v_heq_3066_, v_i_3067_, v_acc_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v_vals_3065_);
lean_dec_ref(v_keys_3064_);
return v_res_3080_;
}
}
uint8_t l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(lean_object* v_a_3081_, lean_object* v_x_3082_){
_start:
{
if (lean_obj_tag(v_x_3082_) == 0)
{
uint8_t v___x_3083_; 
v___x_3083_ = 0;
return v___x_3083_;
}
else
{
lean_object* v_head_3084_; lean_object* v_tail_3085_; uint8_t v___x_3086_; 
v_head_3084_ = lean_ctor_get(v_x_3082_, 0);
v_tail_3085_ = lean_ctor_get(v_x_3082_, 1);
v___x_3086_ = lean_nat_dec_eq(v_a_3081_, v_head_3084_);
if (v___x_3086_ == 0)
{
v_x_3082_ = v_tail_3085_;
goto _start;
}
else
{
return v___x_3086_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3081_ = stack[0].m_obj;
lean_object* v_x_3082_ = stack[1].m_obj;
uint8_t v_res_3088_;
v_res_3088_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_a_3081_, v_x_3082_);
stack->m_num = v_res_3088_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0___boxed(lean_object* v_a_3089_, lean_object* v_x_3090_){
_start:
{
uint8_t v_res_3091_; lean_object* v_r_3092_; 
v_res_3091_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_a_3089_, v_x_3090_);
lean_dec(v_x_3090_);
lean_dec(v_a_3089_);
v_r_3092_ = lean_box(v_res_3091_);
return v_r_3092_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_3096_ = lean_unsigned_to_nat(6u);
v___x_3097_ = lean_unsigned_to_nat(94u);
v___x_3098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3099_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3100_ = l_mkPanicMessageWithDecl(v___x_3099_, v___x_3098_, v___x_3097_, v___x_3096_, v___x_3095_);
return v___x_3100_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3));
v___x_3103_ = lean_unsigned_to_nat(6u);
v___x_3104_ = lean_unsigned_to_nat(91u);
v___x_3105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3106_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3107_ = l_mkPanicMessageWithDecl(v___x_3106_, v___x_3105_, v___x_3104_, v___x_3103_, v___x_3102_);
return v___x_3107_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5));
v___x_3110_ = lean_unsigned_to_nat(6u);
v___x_3111_ = lean_unsigned_to_nat(92u);
v___x_3112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3113_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3114_ = l_mkPanicMessageWithDecl(v___x_3113_, v___x_3112_, v___x_3111_, v___x_3110_, v___x_3109_);
return v___x_3114_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7));
v___x_3117_ = lean_unsigned_to_nat(6u);
v___x_3118_ = lean_unsigned_to_nat(93u);
v___x_3119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3120_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3121_ = l_mkPanicMessageWithDecl(v___x_3120_, v___x_3119_, v___x_3118_, v___x_3117_, v___x_3116_);
return v___x_3121_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(lean_object* v_a_3122_, lean_object* v_as_3123_, size_t v_sz_3124_, size_t v_i_3125_, lean_object* v_b_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_usize_dec_lt(v_i_3125_, v_sz_3124_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v_b_3126_);
return v___x_3139_;
}
else
{
lean_object* v_snd_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3196_; 
v_snd_3140_ = lean_ctor_get(v_b_3126_, 1);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_b_3126_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v_b_3126_, 0);
lean_dec(v_unused_3197_);
v___x_3142_ = v_b_3126_;
v_isShared_3143_ = v_isSharedCheck_3196_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_snd_3140_);
lean_dec(v_b_3126_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3196_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v_a_3146_; lean_object* v___y_3157_; lean_object* v_a_3180_; 
v___x_3144_ = lean_box(0);
v_a_3180_ = lean_array_uget_borrowed(v_as_3123_, v_i_3125_);
if (lean_obj_tag(v_a_3180_) == 1)
{
lean_object* v_val_3181_; lean_object* v_p_3182_; uint8_t v___x_3183_; 
v_val_3181_ = lean_ctor_get(v_a_3180_, 0);
v_p_3182_ = lean_ctor_get(v_val_3181_, 0);
v___x_3183_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3185_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3184_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
v___y_3157_ = v___x_3185_;
goto v___jp_3156_;
}
else
{
uint8_t v___x_3186_; 
v___x_3186_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3182_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3188_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3187_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
v___y_3157_ = v___x_3188_;
goto v___jp_3156_;
}
else
{
lean_object* v_elimStack_3189_; uint8_t v___x_3190_; 
v_elimStack_3189_ = lean_ctor_get(v_a_3122_, 10);
v___x_3190_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3140_, v_elimStack_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3192_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3191_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
v___y_3157_ = v___x_3192_;
goto v___jp_3156_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v___x_3193_ = l_Int_Internal_Linear_Poly_coeff(v_p_3182_, v_snd_3140_);
v___x_3194_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3195_ = lean_int_dec_eq(v___x_3193_, v___x_3194_);
lean_dec(v___x_3193_);
if (v___x_3195_ == 0)
{
if (v___x_3190_ == 0)
{
goto v___jp_3177_;
}
else
{
goto v___jp_3153_;
}
}
else
{
goto v___jp_3177_;
}
}
}
}
}
else
{
goto v___jp_3153_;
}
v___jp_3145_:
{
lean_object* v___x_3148_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 1, v_a_3146_);
lean_ctor_set(v___x_3142_, 0, v___x_3144_);
v___x_3148_ = v___x_3142_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_a_3146_);
v___x_3148_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
size_t v___x_3149_; size_t v___x_3150_; 
v___x_3149_ = ((size_t)1ULL);
v___x_3150_ = lean_usize_add(v_i_3125_, v___x_3149_);
v_i_3125_ = v___x_3150_;
v_b_3126_ = v___x_3148_;
goto _start;
}
}
v___jp_3153_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_unsigned_to_nat(1u);
v___x_3155_ = lean_nat_add(v_snd_3140_, v___x_3154_);
lean_dec(v_snd_3140_);
v_a_3146_ = v___x_3155_;
goto v___jp_3145_;
}
v___jp_3156_:
{
if (lean_obj_tag(v___y_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3168_; 
v_a_3158_ = lean_ctor_get(v___y_3157_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___y_3157_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3160_ = v___y_3157_;
v_isShared_3161_ = v_isSharedCheck_3168_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___y_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3168_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
if (lean_obj_tag(v_a_3158_) == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
lean_del_object(v___x_3142_);
v___x_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_a_3158_);
v___x_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v_snd_3140_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3163_);
v___x_3165_ = v___x_3160_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
else
{
lean_object* v_a_3167_; 
lean_del_object(v___x_3160_);
lean_dec(v_snd_3140_);
v_a_3167_ = lean_ctor_get(v_a_3158_, 0);
lean_inc(v_a_3167_);
lean_dec_ref_known(v_a_3158_, 1);
v_a_3146_ = v_a_3167_;
goto v___jp_3145_;
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_del_object(v___x_3142_);
lean_dec(v_snd_3140_);
v_a_3169_ = lean_ctor_get(v___y_3157_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___y_3157_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___y_3157_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___y_3157_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
v___jp_3177_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3179_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3178_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
v___y_3157_ = v___x_3179_;
goto v___jp_3156_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3122_ = stack[0].m_obj;
lean_object* v_as_3123_ = stack[1].m_obj;
size_t v_sz_3124_ = stack[2].m_num;
size_t v_i_3125_ = stack[3].m_num;
lean_object* v_b_3126_ = stack[4].m_obj;
lean_object* v___y_3127_ = stack[5].m_obj;
lean_object* v___y_3128_ = stack[6].m_obj;
lean_object* v___y_3129_ = stack[7].m_obj;
lean_object* v___y_3130_ = stack[8].m_obj;
lean_object* v___y_3131_ = stack[9].m_obj;
lean_object* v___y_3132_ = stack[10].m_obj;
lean_object* v___y_3133_ = stack[11].m_obj;
lean_object* v___y_3134_ = stack[12].m_obj;
lean_object* v___y_3135_ = stack[13].m_obj;
lean_object* v___y_3136_ = stack[14].m_obj;
lean_object* v_res_3198_;
v_res_3198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3122_, v_as_3123_, v_sz_3124_, v_i_3125_, v_b_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
stack->m_obj
 = v_res_3198_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_a_3199_, lean_object* v_as_3200_, lean_object* v_sz_3201_, lean_object* v_i_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
size_t v_sz_boxed_3215_; size_t v_i_boxed_3216_; lean_object* v_res_3217_; 
v_sz_boxed_3215_ = lean_unbox_usize(v_sz_3201_);
lean_dec(v_sz_3201_);
v_i_boxed_3216_ = lean_unbox_usize(v_i_3202_);
lean_dec(v_i_3202_);
v_res_3217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3199_, v_as_3200_, v_sz_boxed_3215_, v_i_boxed_3216_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v_as_3200_);
lean_dec_ref(v_a_3199_);
return v_res_3217_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(lean_object* v_a_3218_, lean_object* v_as_3219_, size_t v_sz_3220_, size_t v_i_3221_, lean_object* v_b_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_usize_dec_lt(v_i_3221_, v_sz_3220_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3235_, 0, v_b_3222_);
return v___x_3235_;
}
else
{
lean_object* v_snd_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3292_; 
v_snd_3236_ = lean_ctor_get(v_b_3222_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_b_3222_);
if (v_isSharedCheck_3292_ == 0)
{
lean_object* v_unused_3293_; 
v_unused_3293_ = lean_ctor_get(v_b_3222_, 0);
lean_dec(v_unused_3293_);
v___x_3238_ = v_b_3222_;
v_isShared_3239_ = v_isSharedCheck_3292_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_snd_3236_);
lean_dec(v_b_3222_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3292_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v_a_3242_; lean_object* v___y_3253_; lean_object* v_a_3276_; 
v___x_3240_ = lean_box(0);
v_a_3276_ = lean_array_uget_borrowed(v_as_3219_, v_i_3221_);
if (lean_obj_tag(v_a_3276_) == 1)
{
lean_object* v_val_3277_; lean_object* v_p_3278_; uint8_t v___x_3279_; 
v_val_3277_ = lean_ctor_get(v_a_3276_, 0);
v_p_3278_ = lean_ctor_get(v_val_3277_, 0);
v___x_3279_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3281_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3280_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
v___y_3253_ = v___x_3281_;
goto v___jp_3252_;
}
else
{
uint8_t v___x_3282_; 
v___x_3282_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3278_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3284_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3283_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
v___y_3253_ = v___x_3284_;
goto v___jp_3252_;
}
else
{
lean_object* v_elimStack_3285_; uint8_t v___x_3286_; 
v_elimStack_3285_ = lean_ctor_get(v_a_3218_, 10);
v___x_3286_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3236_, v_elimStack_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3288_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3287_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
v___y_3253_ = v___x_3288_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3289_ = l_Int_Internal_Linear_Poly_coeff(v_p_3278_, v_snd_3236_);
v___x_3290_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3291_ = lean_int_dec_eq(v___x_3289_, v___x_3290_);
lean_dec(v___x_3289_);
if (v___x_3291_ == 0)
{
if (v___x_3286_ == 0)
{
goto v___jp_3273_;
}
else
{
goto v___jp_3249_;
}
}
else
{
goto v___jp_3273_;
}
}
}
}
}
else
{
goto v___jp_3249_;
}
v___jp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 1, v_a_3242_);
lean_ctor_set(v___x_3238_, 0, v___x_3240_);
v___x_3244_ = v___x_3238_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_a_3242_);
v___x_3244_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
size_t v___x_3245_; size_t v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = lean_usize_add(v_i_3221_, v___x_3245_);
v___x_3247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3218_, v_as_3219_, v_sz_3220_, v___x_3246_, v___x_3244_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
return v___x_3247_;
}
}
v___jp_3249_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_unsigned_to_nat(1u);
v___x_3251_ = lean_nat_add(v_snd_3236_, v___x_3250_);
lean_dec(v_snd_3236_);
v_a_3242_ = v___x_3251_;
goto v___jp_3241_;
}
v___jp_3252_:
{
if (lean_obj_tag(v___y_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3264_; 
v_a_3254_ = lean_ctor_get(v___y_3253_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___y_3253_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3256_ = v___y_3253_;
v_isShared_3257_ = v_isSharedCheck_3264_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___y_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3264_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
if (lean_obj_tag(v_a_3254_) == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
lean_del_object(v___x_3238_);
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_a_3254_);
v___x_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
lean_ctor_set(v___x_3259_, 1, v_snd_3236_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3259_);
v___x_3261_ = v___x_3256_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
else
{
lean_object* v_a_3263_; 
lean_del_object(v___x_3256_);
lean_dec(v_snd_3236_);
v_a_3263_ = lean_ctor_get(v_a_3254_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v_a_3254_, 1);
v_a_3242_ = v_a_3263_;
goto v___jp_3241_;
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_del_object(v___x_3238_);
lean_dec(v_snd_3236_);
v_a_3265_ = lean_ctor_get(v___y_3253_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___y_3253_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___y_3253_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___y_3253_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
v___jp_3273_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3275_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3274_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
v___y_3253_ = v___x_3275_;
goto v___jp_3252_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3218_ = stack[0].m_obj;
lean_object* v_as_3219_ = stack[1].m_obj;
size_t v_sz_3220_ = stack[2].m_num;
size_t v_i_3221_ = stack[3].m_num;
lean_object* v_b_3222_ = stack[4].m_obj;
lean_object* v___y_3223_ = stack[5].m_obj;
lean_object* v___y_3224_ = stack[6].m_obj;
lean_object* v___y_3225_ = stack[7].m_obj;
lean_object* v___y_3226_ = stack[8].m_obj;
lean_object* v___y_3227_ = stack[9].m_obj;
lean_object* v___y_3228_ = stack[10].m_obj;
lean_object* v___y_3229_ = stack[11].m_obj;
lean_object* v___y_3230_ = stack[12].m_obj;
lean_object* v___y_3231_ = stack[13].m_obj;
lean_object* v___y_3232_ = stack[14].m_obj;
lean_object* v_res_3294_;
v_res_3294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3218_, v_as_3219_, v_sz_3220_, v_i_3221_, v_b_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
stack->m_obj
 = v_res_3294_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3___boxed(lean_object* v_a_3295_, lean_object* v_as_3296_, lean_object* v_sz_3297_, lean_object* v_i_3298_, lean_object* v_b_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
size_t v_sz_boxed_3311_; size_t v_i_boxed_3312_; lean_object* v_res_3313_; 
v_sz_boxed_3311_ = lean_unbox_usize(v_sz_3297_);
lean_dec(v_sz_3297_);
v_i_boxed_3312_ = lean_unbox_usize(v_i_3298_);
lean_dec(v_i_3298_);
v_res_3313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3295_, v_as_3296_, v_sz_boxed_3311_, v_i_boxed_3312_, v_b_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v_as_3296_);
lean_dec_ref(v_a_3295_);
return v_res_3313_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(lean_object* v_init_3314_, lean_object* v_a_3315_, lean_object* v_n_3316_, lean_object* v_b_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
if (lean_obj_tag(v_n_3316_) == 0)
{
lean_object* v_cs_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; size_t v_sz_3332_; size_t v___x_3333_; lean_object* v___x_3334_; 
v_cs_3329_ = lean_ctor_get(v_n_3316_, 0);
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v_b_3317_);
v_sz_3332_ = lean_array_size(v_cs_3329_);
v___x_3333_ = ((size_t)0ULL);
v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3314_, v_a_3315_, v_cs_3329_, v_sz_3332_, v___x_3333_, v___x_3331_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3349_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3349_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3349_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_fst_3339_; 
v_fst_3339_ = lean_ctor_get(v_a_3335_, 0);
if (lean_obj_tag(v_fst_3339_) == 0)
{
lean_object* v_snd_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
v_snd_3340_ = lean_ctor_get(v_a_3335_, 1);
lean_inc(v_snd_3340_);
lean_dec(v_a_3335_);
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_snd_3340_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3341_);
v___x_3343_ = v___x_3337_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
else
{
lean_object* v_val_3345_; lean_object* v___x_3347_; 
lean_inc_ref(v_fst_3339_);
lean_dec(v_a_3335_);
v_val_3345_ = lean_ctor_get(v_fst_3339_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v_fst_3339_, 1);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v_val_3345_);
v___x_3347_ = v___x_3337_;
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
v_a_3350_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3334_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3334_);
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
else
{
lean_object* v_vs_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; size_t v_sz_3361_; size_t v___x_3362_; lean_object* v___x_3363_; 
v_vs_3358_ = lean_ctor_get(v_n_3316_, 0);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
lean_ctor_set(v___x_3360_, 1, v_b_3317_);
v_sz_3361_ = lean_array_size(v_vs_3358_);
v___x_3362_ = ((size_t)0ULL);
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3315_, v_vs_3358_, v_sz_3361_, v___x_3362_, v___x_3360_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3378_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3378_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3378_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_fst_3368_; 
v_fst_3368_ = lean_ctor_get(v_a_3364_, 0);
if (lean_obj_tag(v_fst_3368_) == 0)
{
lean_object* v_snd_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v_snd_3369_ = lean_ctor_get(v_a_3364_, 1);
lean_inc(v_snd_3369_);
lean_dec(v_a_3364_);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_snd_3369_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3370_);
v___x_3372_ = v___x_3366_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
else
{
lean_object* v_val_3374_; lean_object* v___x_3376_; 
lean_inc_ref(v_fst_3368_);
lean_dec(v_a_3364_);
v_val_3374_ = lean_ctor_get(v_fst_3368_, 0);
lean_inc(v_val_3374_);
lean_dec_ref_known(v_fst_3368_, 1);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v_val_3374_);
v___x_3376_ = v___x_3366_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_val_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v_a_3379_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3363_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3363_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3314_ = stack[0].m_obj;
lean_object* v_a_3315_ = stack[1].m_obj;
lean_object* v_n_3316_ = stack[2].m_obj;
lean_object* v_b_3317_ = stack[3].m_obj;
lean_object* v___y_3318_ = stack[4].m_obj;
lean_object* v___y_3319_ = stack[5].m_obj;
lean_object* v___y_3320_ = stack[6].m_obj;
lean_object* v___y_3321_ = stack[7].m_obj;
lean_object* v___y_3322_ = stack[8].m_obj;
lean_object* v___y_3323_ = stack[9].m_obj;
lean_object* v___y_3324_ = stack[10].m_obj;
lean_object* v___y_3325_ = stack[11].m_obj;
lean_object* v___y_3326_ = stack[12].m_obj;
lean_object* v___y_3327_ = stack[13].m_obj;
lean_object* v_res_3387_;
v_res_3387_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3314_, v_a_3315_, v_n_3316_, v_b_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
stack->m_obj
 = v_res_3387_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(lean_object* v_init_3388_, lean_object* v_a_3389_, lean_object* v_as_3390_, size_t v_sz_3391_, size_t v_i_3392_, lean_object* v_b_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
uint8_t v___x_3405_; 
v___x_3405_ = lean_usize_dec_lt(v_i_3392_, v_sz_3391_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3406_, 0, v_b_3393_);
return v___x_3406_;
}
else
{
lean_object* v_snd_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3441_; 
v_snd_3407_ = lean_ctor_get(v_b_3393_, 1);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_b_3393_);
if (v_isSharedCheck_3441_ == 0)
{
lean_object* v_unused_3442_; 
v_unused_3442_ = lean_ctor_get(v_b_3393_, 0);
lean_dec(v_unused_3442_);
v___x_3409_ = v_b_3393_;
v_isShared_3410_ = v_isSharedCheck_3441_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_snd_3407_);
lean_dec(v_b_3393_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3441_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v_a_3412_; lean_object* v___x_3413_; 
v___x_3411_ = lean_box(0);
v_a_3412_ = lean_array_uget_borrowed(v_as_3390_, v_i_3392_);
lean_inc(v_snd_3407_);
v___x_3413_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3388_, v_a_3389_, v_a_3412_, v_snd_3407_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3432_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3432_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3432_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
if (lean_obj_tag(v_a_3414_) == 0)
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_a_3414_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3418_);
v___x_3420_ = v___x_3409_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_snd_3407_);
v___x_3420_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3420_);
v___x_3422_ = v___x_3416_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; 
lean_del_object(v___x_3416_);
lean_dec(v_snd_3407_);
v_a_3425_ = lean_ctor_get(v_a_3414_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v_a_3414_, 1);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 1, v_a_3425_);
lean_ctor_set(v___x_3409_, 0, v___x_3411_);
v___x_3427_ = v___x_3409_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_a_3425_);
v___x_3427_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
size_t v___x_3428_; size_t v___x_3429_; 
v___x_3428_ = ((size_t)1ULL);
v___x_3429_ = lean_usize_add(v_i_3392_, v___x_3428_);
v_i_3392_ = v___x_3429_;
v_b_3393_ = v___x_3427_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_del_object(v___x_3409_);
lean_dec(v_snd_3407_);
v_a_3433_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3413_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3413_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3388_ = stack[0].m_obj;
lean_object* v_a_3389_ = stack[1].m_obj;
lean_object* v_as_3390_ = stack[2].m_obj;
size_t v_sz_3391_ = stack[3].m_num;
size_t v_i_3392_ = stack[4].m_num;
lean_object* v_b_3393_ = stack[5].m_obj;
lean_object* v___y_3394_ = stack[6].m_obj;
lean_object* v___y_3395_ = stack[7].m_obj;
lean_object* v___y_3396_ = stack[8].m_obj;
lean_object* v___y_3397_ = stack[9].m_obj;
lean_object* v___y_3398_ = stack[10].m_obj;
lean_object* v___y_3399_ = stack[11].m_obj;
lean_object* v___y_3400_ = stack[12].m_obj;
lean_object* v___y_3401_ = stack[13].m_obj;
lean_object* v___y_3402_ = stack[14].m_obj;
lean_object* v___y_3403_ = stack[15].m_obj;
lean_object* v_res_3443_;
v_res_3443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3388_, v_a_3389_, v_as_3390_, v_sz_3391_, v_i_3392_, v_b_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
stack->m_obj
 = v_res_3443_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_3444_ = _args[0];
lean_object* v_a_3445_ = _args[1];
lean_object* v_as_3446_ = _args[2];
lean_object* v_sz_3447_ = _args[3];
lean_object* v_i_3448_ = _args[4];
lean_object* v_b_3449_ = _args[5];
lean_object* v___y_3450_ = _args[6];
lean_object* v___y_3451_ = _args[7];
lean_object* v___y_3452_ = _args[8];
lean_object* v___y_3453_ = _args[9];
lean_object* v___y_3454_ = _args[10];
lean_object* v___y_3455_ = _args[11];
lean_object* v___y_3456_ = _args[12];
lean_object* v___y_3457_ = _args[13];
lean_object* v___y_3458_ = _args[14];
lean_object* v___y_3459_ = _args[15];
lean_object* v___y_3460_ = _args[16];
_start:
{
size_t v_sz_boxed_3461_; size_t v_i_boxed_3462_; lean_object* v_res_3463_; 
v_sz_boxed_3461_ = lean_unbox_usize(v_sz_3447_);
lean_dec(v_sz_3447_);
v_i_boxed_3462_ = lean_unbox_usize(v_i_3448_);
lean_dec(v_i_3448_);
v_res_3463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3444_, v_a_3445_, v_as_3446_, v_sz_boxed_3461_, v_i_boxed_3462_, v_b_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v_as_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_init_3444_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1___boxed(lean_object* v_init_3464_, lean_object* v_a_3465_, lean_object* v_n_3466_, lean_object* v_b_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3464_, v_a_3465_, v_n_3466_, v_b_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v_n_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_init_3464_);
return v_res_3479_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(lean_object* v_a_3480_, lean_object* v_as_3481_, size_t v_sz_3482_, size_t v_i_3483_, lean_object* v_b_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_usize_dec_lt(v_i_3483_, v_sz_3482_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v_b_3484_);
return v___x_3497_;
}
else
{
lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3561_; 
v_snd_3498_ = lean_ctor_get(v_b_3484_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_b_3484_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; 
v_unused_3562_ = lean_ctor_get(v_b_3484_, 0);
lean_dec(v_unused_3562_);
v___x_3500_ = v_b_3484_;
v_isShared_3501_ = v_isSharedCheck_3561_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_dec(v_b_3484_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3561_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v_a_3504_; lean_object* v___y_3515_; lean_object* v_a_3545_; 
v___x_3502_ = lean_box(0);
v_a_3545_ = lean_array_uget_borrowed(v_as_3481_, v_i_3483_);
if (lean_obj_tag(v_a_3545_) == 1)
{
lean_object* v_val_3546_; lean_object* v_p_3547_; uint8_t v___x_3548_; 
v_val_3546_ = lean_ctor_get(v_a_3545_, 0);
v_p_3547_ = lean_ctor_get(v_val_3546_, 0);
v___x_3548_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3550_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3549_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
v___y_3515_ = v___x_3550_;
goto v___jp_3514_;
}
else
{
uint8_t v___x_3551_; 
v___x_3551_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3547_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3553_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3552_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
v___y_3515_ = v___x_3553_;
goto v___jp_3514_;
}
else
{
lean_object* v_elimStack_3554_; uint8_t v___x_3555_; 
v_elimStack_3554_ = lean_ctor_get(v_a_3480_, 10);
v___x_3555_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3498_, v_elimStack_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3557_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3556_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
v___y_3515_ = v___x_3557_;
goto v___jp_3514_;
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3558_ = l_Int_Internal_Linear_Poly_coeff(v_p_3547_, v_snd_3498_);
v___x_3559_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3560_ = lean_int_dec_eq(v___x_3558_, v___x_3559_);
lean_dec(v___x_3558_);
if (v___x_3560_ == 0)
{
if (v___x_3555_ == 0)
{
goto v___jp_3542_;
}
else
{
goto v___jp_3511_;
}
}
else
{
goto v___jp_3542_;
}
}
}
}
}
else
{
goto v___jp_3511_;
}
v___jp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v_a_3504_);
lean_ctor_set(v___x_3500_, 0, v___x_3502_);
v___x_3506_ = v___x_3500_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_a_3504_);
v___x_3506_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
size_t v___x_3507_; size_t v___x_3508_; 
v___x_3507_ = ((size_t)1ULL);
v___x_3508_ = lean_usize_add(v_i_3483_, v___x_3507_);
v_i_3483_ = v___x_3508_;
v_b_3484_ = v___x_3506_;
goto _start;
}
}
v___jp_3511_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = lean_unsigned_to_nat(1u);
v___x_3513_ = lean_nat_add(v_snd_3498_, v___x_3512_);
lean_dec(v_snd_3498_);
v_a_3504_ = v___x_3513_;
goto v___jp_3503_;
}
v___jp_3514_:
{
if (lean_obj_tag(v___y_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3533_; 
v_a_3516_ = lean_ctor_get(v___y_3515_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___y_3515_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3518_ = v___y_3515_;
v_isShared_3519_ = v_isSharedCheck_3533_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___y_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3533_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
if (lean_obj_tag(v_a_3516_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3531_; 
lean_del_object(v___x_3500_);
v_a_3520_ = lean_ctor_get(v_a_3516_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_a_3516_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3522_ = v_a_3516_;
v_isShared_3523_ = v_isSharedCheck_3531_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v_a_3516_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3531_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set_tag(v___x_3522_, 1);
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
lean_ctor_set(v___x_3526_, 1, v_snd_3498_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3526_);
v___x_3528_ = v___x_3518_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_a_3532_; 
lean_del_object(v___x_3518_);
lean_dec(v_snd_3498_);
v_a_3532_ = lean_ctor_get(v_a_3516_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v_a_3516_, 1);
v_a_3504_ = v_a_3532_;
goto v___jp_3503_;
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
v_a_3534_ = lean_ctor_get(v___y_3515_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___y_3515_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___y_3515_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___y_3515_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
v___jp_3542_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3544_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3543_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
v___y_3515_ = v___x_3544_;
goto v___jp_3514_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3480_ = stack[0].m_obj;
lean_object* v_as_3481_ = stack[1].m_obj;
size_t v_sz_3482_ = stack[2].m_num;
size_t v_i_3483_ = stack[3].m_num;
lean_object* v_b_3484_ = stack[4].m_obj;
lean_object* v___y_3485_ = stack[5].m_obj;
lean_object* v___y_3486_ = stack[6].m_obj;
lean_object* v___y_3487_ = stack[7].m_obj;
lean_object* v___y_3488_ = stack[8].m_obj;
lean_object* v___y_3489_ = stack[9].m_obj;
lean_object* v___y_3490_ = stack[10].m_obj;
lean_object* v___y_3491_ = stack[11].m_obj;
lean_object* v___y_3492_ = stack[12].m_obj;
lean_object* v___y_3493_ = stack[13].m_obj;
lean_object* v___y_3494_ = stack[14].m_obj;
lean_object* v_res_3563_;
v_res_3563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3480_, v_as_3481_, v_sz_3482_, v_i_3483_, v_b_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
stack->m_obj
 = v_res_3563_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5___boxed(lean_object* v_a_3564_, lean_object* v_as_3565_, lean_object* v_sz_3566_, lean_object* v_i_3567_, lean_object* v_b_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
size_t v_sz_boxed_3580_; size_t v_i_boxed_3581_; lean_object* v_res_3582_; 
v_sz_boxed_3580_ = lean_unbox_usize(v_sz_3566_);
lean_dec(v_sz_3566_);
v_i_boxed_3581_ = lean_unbox_usize(v_i_3567_);
lean_dec(v_i_3567_);
v_res_3582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3564_, v_as_3565_, v_sz_boxed_3580_, v_i_boxed_3581_, v_b_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v_as_3565_);
lean_dec_ref(v_a_3564_);
return v_res_3582_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(lean_object* v_a_3583_, lean_object* v_as_3584_, size_t v_sz_3585_, size_t v_i_3586_, lean_object* v_b_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
uint8_t v___x_3599_; 
v___x_3599_ = lean_usize_dec_lt(v_i_3586_, v_sz_3585_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3600_, 0, v_b_3587_);
return v___x_3600_;
}
else
{
lean_object* v_snd_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3664_; 
v_snd_3601_ = lean_ctor_get(v_b_3587_, 1);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_b_3587_);
if (v_isSharedCheck_3664_ == 0)
{
lean_object* v_unused_3665_; 
v_unused_3665_ = lean_ctor_get(v_b_3587_, 0);
lean_dec(v_unused_3665_);
v___x_3603_ = v_b_3587_;
v_isShared_3604_ = v_isSharedCheck_3664_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_snd_3601_);
lean_dec(v_b_3587_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3664_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v_a_3607_; lean_object* v___y_3618_; lean_object* v_a_3648_; 
v___x_3605_ = lean_box(0);
v_a_3648_ = lean_array_uget_borrowed(v_as_3584_, v_i_3586_);
if (lean_obj_tag(v_a_3648_) == 1)
{
lean_object* v_val_3649_; lean_object* v_p_3650_; uint8_t v___x_3651_; 
v_val_3649_ = lean_ctor_get(v_a_3648_, 0);
v_p_3650_ = lean_ctor_get(v_val_3649_, 0);
v___x_3651_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3653_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3652_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
v___y_3618_ = v___x_3653_;
goto v___jp_3617_;
}
else
{
uint8_t v___x_3654_; 
v___x_3654_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3650_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3656_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3655_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
v___y_3618_ = v___x_3656_;
goto v___jp_3617_;
}
else
{
lean_object* v_elimStack_3657_; uint8_t v___x_3658_; 
v_elimStack_3657_ = lean_ctor_get(v_a_3583_, 10);
v___x_3658_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3601_, v_elimStack_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3660_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3659_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
v___y_3618_ = v___x_3660_;
goto v___jp_3617_;
}
else
{
lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3661_ = l_Int_Internal_Linear_Poly_coeff(v_p_3650_, v_snd_3601_);
v___x_3662_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3663_ = lean_int_dec_eq(v___x_3661_, v___x_3662_);
lean_dec(v___x_3661_);
if (v___x_3663_ == 0)
{
if (v___x_3658_ == 0)
{
goto v___jp_3645_;
}
else
{
goto v___jp_3614_;
}
}
else
{
goto v___jp_3645_;
}
}
}
}
}
else
{
goto v___jp_3614_;
}
v___jp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 1, v_a_3607_);
lean_ctor_set(v___x_3603_, 0, v___x_3605_);
v___x_3609_ = v___x_3603_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_a_3607_);
v___x_3609_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
size_t v___x_3610_; size_t v___x_3611_; lean_object* v___x_3612_; 
v___x_3610_ = ((size_t)1ULL);
v___x_3611_ = lean_usize_add(v_i_3586_, v___x_3610_);
v___x_3612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3583_, v_as_3584_, v_sz_3585_, v___x_3611_, v___x_3609_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
return v___x_3612_;
}
}
v___jp_3614_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_unsigned_to_nat(1u);
v___x_3616_ = lean_nat_add(v_snd_3601_, v___x_3615_);
lean_dec(v_snd_3601_);
v_a_3607_ = v___x_3616_;
goto v___jp_3606_;
}
v___jp_3617_:
{
if (lean_obj_tag(v___y_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3636_; 
v_a_3619_ = lean_ctor_get(v___y_3618_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___y_3618_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3621_ = v___y_3618_;
v_isShared_3622_ = v_isSharedCheck_3636_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___y_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3636_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
if (lean_obj_tag(v_a_3619_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3634_; 
lean_del_object(v___x_3603_);
v_a_3623_ = lean_ctor_get(v_a_3619_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_a_3619_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3625_ = v_a_3619_;
v_isShared_3626_ = v_isSharedCheck_3634_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v_a_3619_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3634_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 1);
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
lean_ctor_set(v___x_3629_, 1, v_snd_3601_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v___x_3629_);
v___x_3631_ = v___x_3621_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_object* v_a_3635_; 
lean_del_object(v___x_3621_);
lean_dec(v_snd_3601_);
v_a_3635_ = lean_ctor_get(v_a_3619_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v_a_3619_, 1);
v_a_3607_ = v_a_3635_;
goto v___jp_3606_;
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_del_object(v___x_3603_);
lean_dec(v_snd_3601_);
v_a_3637_ = lean_ctor_get(v___y_3618_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___y_3618_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___y_3618_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___y_3618_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
v___jp_3645_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3647_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3646_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
v___y_3618_ = v___x_3647_;
goto v___jp_3617_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3583_ = stack[0].m_obj;
lean_object* v_as_3584_ = stack[1].m_obj;
size_t v_sz_3585_ = stack[2].m_num;
size_t v_i_3586_ = stack[3].m_num;
lean_object* v_b_3587_ = stack[4].m_obj;
lean_object* v___y_3588_ = stack[5].m_obj;
lean_object* v___y_3589_ = stack[6].m_obj;
lean_object* v___y_3590_ = stack[7].m_obj;
lean_object* v___y_3591_ = stack[8].m_obj;
lean_object* v___y_3592_ = stack[9].m_obj;
lean_object* v___y_3593_ = stack[10].m_obj;
lean_object* v___y_3594_ = stack[11].m_obj;
lean_object* v___y_3595_ = stack[12].m_obj;
lean_object* v___y_3596_ = stack[13].m_obj;
lean_object* v___y_3597_ = stack[14].m_obj;
lean_object* v_res_3666_;
v_res_3666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3583_, v_as_3584_, v_sz_3585_, v_i_3586_, v_b_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
stack->m_obj
 = v_res_3666_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2___boxed(lean_object* v_a_3667_, lean_object* v_as_3668_, lean_object* v_sz_3669_, lean_object* v_i_3670_, lean_object* v_b_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
size_t v_sz_boxed_3683_; size_t v_i_boxed_3684_; lean_object* v_res_3685_; 
v_sz_boxed_3683_ = lean_unbox_usize(v_sz_3669_);
lean_dec(v_sz_3669_);
v_i_boxed_3684_ = lean_unbox_usize(v_i_3670_);
lean_dec(v_i_3670_);
v_res_3685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3667_, v_as_3668_, v_sz_boxed_3683_, v_i_boxed_3684_, v_b_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v_as_3668_);
lean_dec_ref(v_a_3667_);
return v_res_3685_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(lean_object* v_a_3686_, lean_object* v_t_3687_, lean_object* v_init_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_root_3700_; lean_object* v_tail_3701_; lean_object* v___x_3702_; 
v_root_3700_ = lean_ctor_get(v_t_3687_, 0);
v_tail_3701_ = lean_ctor_get(v_t_3687_, 1);
lean_inc(v_init_3688_);
v___x_3702_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3688_, v_a_3686_, v_root_3700_, v_init_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v_init_3688_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3739_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3739_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3739_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
if (lean_obj_tag(v_a_3703_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3709_; 
v_a_3707_ = lean_ctor_get(v_a_3703_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v_a_3703_, 1);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v_a_3707_);
v___x_3709_ = v___x_3705_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; size_t v_sz_3714_; size_t v___x_3715_; lean_object* v___x_3716_; 
lean_del_object(v___x_3705_);
v_a_3711_ = lean_ctor_get(v_a_3703_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v_a_3703_, 1);
v___x_3712_ = lean_box(0);
v___x_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v_a_3711_);
v_sz_3714_ = lean_array_size(v_tail_3701_);
v___x_3715_ = ((size_t)0ULL);
v___x_3716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3686_, v_tail_3701_, v_sz_3714_, v___x_3715_, v___x_3713_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3730_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3719_ = v___x_3716_;
v_isShared_3720_ = v_isSharedCheck_3730_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3730_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v_fst_3721_; 
v_fst_3721_ = lean_ctor_get(v_a_3717_, 0);
if (lean_obj_tag(v_fst_3721_) == 0)
{
lean_object* v_snd_3722_; lean_object* v___x_3724_; 
v_snd_3722_ = lean_ctor_get(v_a_3717_, 1);
lean_inc(v_snd_3722_);
lean_dec(v_a_3717_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v_snd_3722_);
v___x_3724_ = v___x_3719_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_snd_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
else
{
lean_object* v_val_3726_; lean_object* v___x_3728_; 
lean_inc_ref(v_fst_3721_);
lean_dec(v_a_3717_);
v_val_3726_ = lean_ctor_get(v_fst_3721_, 0);
lean_inc(v_val_3726_);
lean_dec_ref_known(v_fst_3721_, 1);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v_val_3726_);
v___x_3728_ = v___x_3719_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_val_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3716_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3716_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
v_a_3740_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3702_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3702_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3686_ = stack[0].m_obj;
lean_object* v_t_3687_ = stack[1].m_obj;
lean_object* v_init_3688_ = stack[2].m_obj;
lean_object* v___y_3689_ = stack[3].m_obj;
lean_object* v___y_3690_ = stack[4].m_obj;
lean_object* v___y_3691_ = stack[5].m_obj;
lean_object* v___y_3692_ = stack[6].m_obj;
lean_object* v___y_3693_ = stack[7].m_obj;
lean_object* v___y_3694_ = stack[8].m_obj;
lean_object* v___y_3695_ = stack[9].m_obj;
lean_object* v___y_3696_ = stack[10].m_obj;
lean_object* v___y_3697_ = stack[11].m_obj;
lean_object* v___y_3698_ = stack[12].m_obj;
lean_object* v_res_3748_;
v_res_3748_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3686_, v_t_3687_, v_init_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
stack->m_obj
 = v_res_3748_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1___boxed(lean_object* v_a_3749_, lean_object* v_t_3750_, lean_object* v_init_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3749_, v_t_3750_, v_init_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v_t_3750_);
lean_dec_ref(v_a_3749_);
return v_res_3763_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3765_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0));
v___x_3766_ = lean_unsigned_to_nat(2u);
v___x_3767_ = lean_unsigned_to_nat(87u);
v___x_3768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3769_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3770_ = l_mkPanicMessageWithDecl(v___x_3769_, v___x_3768_, v___x_3767_, v___x_3766_, v___x_3765_);
return v___x_3770_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3771_, v_a_3779_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v_elimEqs_3784_; lean_object* v_vars_3785_; lean_object* v_size_3786_; lean_object* v_size_3787_; uint8_t v___x_3788_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v_elimEqs_3784_ = lean_ctor_get(v_a_3783_, 9);
lean_inc_ref(v_elimEqs_3784_);
v_vars_3785_ = lean_ctor_get(v_a_3783_, 0);
v_size_3786_ = lean_ctor_get(v_elimEqs_3784_, 2);
v_size_3787_ = lean_ctor_get(v_vars_3785_, 2);
v___x_3788_ = lean_nat_dec_eq(v_size_3786_, v_size_3787_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_dec_ref(v_elimEqs_3784_);
lean_dec(v_a_3783_);
v___x_3789_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1);
v___x_3790_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_3789_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_unsigned_to_nat(0u);
v___x_3792_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3783_, v_elimEqs_3784_, v___x_3791_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec_ref(v_elimEqs_3784_);
lean_dec(v_a_3783_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3800_; 
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; 
v_unused_3801_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3801_);
v___x_3794_ = v___x_3792_;
v_isShared_3795_ = v_isSharedCheck_3800_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v___x_3792_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3800_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = lean_box(0);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 0, v___x_3796_);
v___x_3798_ = v___x_3794_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
v_a_3802_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3792_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3792_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
v_a_3810_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3782_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3782_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3771_ = stack[0].m_obj;
lean_object* v_a_3772_ = stack[1].m_obj;
lean_object* v_a_3773_ = stack[2].m_obj;
lean_object* v_a_3774_ = stack[3].m_obj;
lean_object* v_a_3775_ = stack[4].m_obj;
lean_object* v_a_3776_ = stack[5].m_obj;
lean_object* v_a_3777_ = stack[6].m_obj;
lean_object* v_a_3778_ = stack[7].m_obj;
lean_object* v_a_3779_ = stack[8].m_obj;
lean_object* v_a_3780_ = stack[9].m_obj;
lean_object* v_res_3818_;
v_res_3818_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
stack->m_obj
 = v_res_3818_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___boxed(lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
lean_dec_ref(v_a_3823_);
lean_dec(v_a_3822_);
lean_dec_ref(v_a_3821_);
lean_dec(v_a_3820_);
lean_dec(v_a_3819_);
return v_res_3830_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3833_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1));
v___x_3834_ = lean_unsigned_to_nat(4u);
v___x_3835_ = lean_unsigned_to_nat(99u);
v___x_3836_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0));
v___x_3837_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3838_ = l_mkPanicMessageWithDecl(v___x_3837_, v___x_3836_, v___x_3835_, v___x_3834_, v___x_3833_);
return v___x_3838_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(lean_object* v_as_x27_3839_, lean_object* v_b_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
if (lean_obj_tag(v_as_x27_3839_) == 0)
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_b_3840_);
return v___x_3852_;
}
else
{
lean_object* v_head_3853_; lean_object* v_tail_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_head_3853_ = lean_ctor_get(v_as_x27_3839_, 0);
v_tail_3854_ = lean_ctor_get(v_as_x27_3839_, 1);
v___x_3855_ = lean_box(0);
v___x_3856_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_head_3853_, v___y_3841_, v___y_3849_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; uint8_t v___x_3858_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = lean_unbox(v_a_3857_);
lean_dec(v_a_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2);
v___x_3860_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_3859_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
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
lean_dec_ref_known(v_a_3861_, 1);
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
lean_dec_ref_known(v_a_3861_, 1);
v_as_x27_3839_ = v_tail_3854_;
v_b_3840_ = v_a_3869_;
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
v_as_x27_3839_ = v_tail_3854_;
v_b_3840_ = v___x_3855_;
goto _start;
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
v_a_3881_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3856_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3856_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_3839_ = stack[0].m_obj;
lean_object* v_b_3840_ = stack[1].m_obj;
lean_object* v___y_3841_ = stack[2].m_obj;
lean_object* v___y_3842_ = stack[3].m_obj;
lean_object* v___y_3843_ = stack[4].m_obj;
lean_object* v___y_3844_ = stack[5].m_obj;
lean_object* v___y_3845_ = stack[6].m_obj;
lean_object* v___y_3846_ = stack[7].m_obj;
lean_object* v___y_3847_ = stack[8].m_obj;
lean_object* v___y_3848_ = stack[9].m_obj;
lean_object* v___y_3849_ = stack[10].m_obj;
lean_object* v___y_3850_ = stack[11].m_obj;
lean_object* v_res_3889_;
v_res_3889_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3839_, v_b_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
stack->m_obj
 = v_res_3889_;
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3904_, v_a_3912_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v_elimStack_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v_elimStack_3917_ = lean_ctor_get(v_a_3916_, 10);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3904_ = stack[0].m_obj;
lean_object* v_a_3905_ = stack[1].m_obj;
lean_object* v_a_3906_ = stack[2].m_obj;
lean_object* v_a_3907_ = stack[3].m_obj;
lean_object* v_a_3908_ = stack[4].m_obj;
lean_object* v_a_3909_ = stack[5].m_obj;
lean_object* v_a_3910_ = stack[6].m_obj;
lean_object* v_a_3911_ = stack[7].m_obj;
lean_object* v_a_3912_ = stack[8].m_obj;
lean_object* v_a_3913_ = stack[9].m_obj;
lean_object* v_res_3936_;
v_res_3936_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
stack->m_obj
 = v_res_3936_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack___boxed(lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec(v_a_3937_);
return v_res_3948_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(lean_object* v_as_3949_, lean_object* v_as_x27_3950_, lean_object* v_b_3951_, lean_object* v_a_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3950_, v_b_3951_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3949_ = stack[0].m_obj;
lean_object* v_as_x27_3950_ = stack[1].m_obj;
lean_object* v_b_3951_ = stack[2].m_obj;
lean_object* v___y_3953_ = stack[4].m_obj;
lean_object* v___y_3954_ = stack[5].m_obj;
lean_object* v___y_3955_ = stack[6].m_obj;
lean_object* v___y_3956_ = stack[7].m_obj;
lean_object* v___y_3957_ = stack[8].m_obj;
lean_object* v___y_3958_ = stack[9].m_obj;
lean_object* v___y_3959_ = stack[10].m_obj;
lean_object* v___y_3960_ = stack[11].m_obj;
lean_object* v___y_3961_ = stack[12].m_obj;
lean_object* v___y_3962_ = stack[13].m_obj;
lean_object* v_res_3965_;
v_res_3965_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(v_as_3949_, v_as_x27_3950_, v_b_3951_, lean_box(0), v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
stack->m_obj
 = v_res_3965_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___boxed(lean_object* v_as_3966_, lean_object* v_as_x27_3967_, lean_object* v_b_3968_, lean_object* v_a_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(v_as_3966_, v_as_x27_3967_, v_b_3968_, v_a_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec(v_as_x27_3967_);
lean_dec(v_as_3966_);
return v_res_3981_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_3985_, lean_object* v_as_3986_, size_t v_sz_3987_, size_t v_i_3988_, lean_object* v_b_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
uint8_t v___x_4001_; 
v___x_4001_ = lean_usize_dec_lt(v_i_3988_, v_sz_3987_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v_b_3989_);
return v___x_4002_;
}
else
{
lean_object* v_a_4003_; lean_object* v_p_4004_; lean_object* v___x_4005_; 
lean_dec_ref(v_b_3989_);
v_a_4003_ = lean_array_uget_borrowed(v_as_3986_, v_i_3988_);
v_p_4004_ = lean_ctor_get(v_a_4003_, 0);
v___x_4005_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4004_, v_____s_3985_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v___x_4006_; size_t v___x_4007_; size_t v___x_4008_; 
lean_dec_ref_known(v___x_4005_, 1);
v___x_4006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_4007_ = ((size_t)1ULL);
v___x_4008_ = lean_usize_add(v_i_3988_, v___x_4007_);
v_i_3988_ = v___x_4008_;
v_b_3989_ = v___x_4006_;
goto _start;
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
v_a_4010_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4005_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4005_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_3985_ = stack[0].m_obj;
lean_object* v_as_3986_ = stack[1].m_obj;
size_t v_sz_3987_ = stack[2].m_num;
size_t v_i_3988_ = stack[3].m_num;
lean_object* v_b_3989_ = stack[4].m_obj;
lean_object* v___y_3990_ = stack[5].m_obj;
lean_object* v___y_3991_ = stack[6].m_obj;
lean_object* v___y_3992_ = stack[7].m_obj;
lean_object* v___y_3993_ = stack[8].m_obj;
lean_object* v___y_3994_ = stack[9].m_obj;
lean_object* v___y_3995_ = stack[10].m_obj;
lean_object* v___y_3996_ = stack[11].m_obj;
lean_object* v___y_3997_ = stack[12].m_obj;
lean_object* v___y_3998_ = stack[13].m_obj;
lean_object* v___y_3999_ = stack[14].m_obj;
lean_object* v_res_4018_;
v_res_4018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3985_, v_as_3986_, v_sz_3987_, v_i_3988_, v_b_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
stack->m_obj
 = v_res_4018_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object* v_____s_4019_, lean_object* v_as_4020_, lean_object* v_sz_4021_, lean_object* v_i_4022_, lean_object* v_b_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
size_t v_sz_boxed_4035_; size_t v_i_boxed_4036_; lean_object* v_res_4037_; 
v_sz_boxed_4035_ = lean_unbox_usize(v_sz_4021_);
lean_dec(v_sz_4021_);
v_i_boxed_4036_ = lean_unbox_usize(v_i_4022_);
lean_dec(v_i_4022_);
v_res_4037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_4019_, v_as_4020_, v_sz_boxed_4035_, v_i_boxed_4036_, v_b_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v_as_4020_);
lean_dec(v_____s_4019_);
return v_res_4037_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_4038_, lean_object* v_as_4039_, size_t v_sz_4040_, size_t v_i_4041_, lean_object* v_b_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
uint8_t v___x_4054_; 
v___x_4054_ = lean_usize_dec_lt(v_i_4041_, v_sz_4040_);
if (v___x_4054_ == 0)
{
lean_object* v___x_4055_; 
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v_b_4042_);
return v___x_4055_;
}
else
{
lean_object* v_a_4056_; lean_object* v_p_4057_; lean_object* v___x_4058_; 
lean_dec_ref(v_b_4042_);
v_a_4056_ = lean_array_uget_borrowed(v_as_4039_, v_i_4041_);
v_p_4057_ = lean_ctor_get(v_a_4056_, 0);
v___x_4058_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4057_, v_____s_4038_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v___x_4059_; size_t v___x_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
lean_dec_ref_known(v___x_4058_, 1);
v___x_4059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_4060_ = ((size_t)1ULL);
v___x_4061_ = lean_usize_add(v_i_4041_, v___x_4060_);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_4038_, v_as_4039_, v_sz_4040_, v___x_4061_, v___x_4059_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
return v___x_4062_;
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
v_a_4063_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4058_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4058_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_4038_ = stack[0].m_obj;
lean_object* v_as_4039_ = stack[1].m_obj;
size_t v_sz_4040_ = stack[2].m_num;
size_t v_i_4041_ = stack[3].m_num;
lean_object* v_b_4042_ = stack[4].m_obj;
lean_object* v___y_4043_ = stack[5].m_obj;
lean_object* v___y_4044_ = stack[6].m_obj;
lean_object* v___y_4045_ = stack[7].m_obj;
lean_object* v___y_4046_ = stack[8].m_obj;
lean_object* v___y_4047_ = stack[9].m_obj;
lean_object* v___y_4048_ = stack[10].m_obj;
lean_object* v___y_4049_ = stack[11].m_obj;
lean_object* v___y_4050_ = stack[12].m_obj;
lean_object* v___y_4051_ = stack[13].m_obj;
lean_object* v___y_4052_ = stack[14].m_obj;
lean_object* v_res_4071_;
v_res_4071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4038_, v_as_4039_, v_sz_4040_, v_i_4041_, v_b_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
stack->m_obj
 = v_res_4071_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object* v_____s_4072_, lean_object* v_as_4073_, lean_object* v_sz_4074_, lean_object* v_i_4075_, lean_object* v_b_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
size_t v_sz_boxed_4088_; size_t v_i_boxed_4089_; lean_object* v_res_4090_; 
v_sz_boxed_4088_ = lean_unbox_usize(v_sz_4074_);
lean_dec(v_sz_4074_);
v_i_boxed_4089_ = lean_unbox_usize(v_i_4075_);
lean_dec(v_i_4075_);
v_res_4090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4072_, v_as_4073_, v_sz_boxed_4088_, v_i_boxed_4089_, v_b_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v_as_4073_);
lean_dec(v_____s_4072_);
return v_res_4090_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_4094_, lean_object* v_as_4095_, size_t v_sz_4096_, size_t v_i_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
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
v___x_4114_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4113_, v_____s_4094_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v___x_4115_; size_t v___x_4116_; size_t v___x_4117_; 
lean_dec_ref_known(v___x_4114_, 1);
v___x_4115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4116_ = ((size_t)1ULL);
v___x_4117_ = lean_usize_add(v_i_4097_, v___x_4116_);
v_i_4097_ = v___x_4117_;
v_b_4098_ = v___x_4115_;
goto _start;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_4094_ = stack[0].m_obj;
lean_object* v_as_4095_ = stack[1].m_obj;
size_t v_sz_4096_ = stack[2].m_num;
size_t v_i_4097_ = stack[3].m_num;
lean_object* v_b_4098_ = stack[4].m_obj;
lean_object* v___y_4099_ = stack[5].m_obj;
lean_object* v___y_4100_ = stack[6].m_obj;
lean_object* v___y_4101_ = stack[7].m_obj;
lean_object* v___y_4102_ = stack[8].m_obj;
lean_object* v___y_4103_ = stack[9].m_obj;
lean_object* v___y_4104_ = stack[10].m_obj;
lean_object* v___y_4105_ = stack[11].m_obj;
lean_object* v___y_4106_ = stack[12].m_obj;
lean_object* v___y_4107_ = stack[13].m_obj;
lean_object* v___y_4108_ = stack[14].m_obj;
lean_object* v_res_4127_;
v_res_4127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4094_, v_as_4095_, v_sz_4096_, v_i_4097_, v_b_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
stack->m_obj
 = v_res_4127_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_____s_4128_, lean_object* v_as_4129_, lean_object* v_sz_4130_, lean_object* v_i_4131_, lean_object* v_b_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
size_t v_sz_boxed_4144_; size_t v_i_boxed_4145_; lean_object* v_res_4146_; 
v_sz_boxed_4144_ = lean_unbox_usize(v_sz_4130_);
lean_dec(v_sz_4130_);
v_i_boxed_4145_ = lean_unbox_usize(v_i_4131_);
lean_dec(v_i_4131_);
v_res_4146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4128_, v_as_4129_, v_sz_boxed_4144_, v_i_boxed_4145_, v_b_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v_as_4129_);
lean_dec(v_____s_4128_);
return v_res_4146_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_4147_, lean_object* v_as_4148_, size_t v_sz_4149_, size_t v_i_4150_, lean_object* v_b_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
uint8_t v___x_4163_; 
v___x_4163_ = lean_usize_dec_lt(v_i_4150_, v_sz_4149_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v_b_4151_);
return v___x_4164_;
}
else
{
lean_object* v_a_4165_; lean_object* v_p_4166_; lean_object* v___x_4167_; 
lean_dec_ref(v_b_4151_);
v_a_4165_ = lean_array_uget_borrowed(v_as_4148_, v_i_4150_);
v_p_4166_ = lean_ctor_get(v_a_4165_, 0);
v___x_4167_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4166_, v_____s_4147_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v___x_4168_; size_t v___x_4169_; size_t v___x_4170_; lean_object* v___x_4171_; 
lean_dec_ref_known(v___x_4167_, 1);
v___x_4168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4169_ = ((size_t)1ULL);
v___x_4170_ = lean_usize_add(v_i_4150_, v___x_4169_);
v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4147_, v_as_4148_, v_sz_4149_, v___x_4170_, v___x_4168_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
return v___x_4171_;
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
v_a_4172_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4167_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4167_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_4147_ = stack[0].m_obj;
lean_object* v_as_4148_ = stack[1].m_obj;
size_t v_sz_4149_ = stack[2].m_num;
size_t v_i_4150_ = stack[3].m_num;
lean_object* v_b_4151_ = stack[4].m_obj;
lean_object* v___y_4152_ = stack[5].m_obj;
lean_object* v___y_4153_ = stack[6].m_obj;
lean_object* v___y_4154_ = stack[7].m_obj;
lean_object* v___y_4155_ = stack[8].m_obj;
lean_object* v___y_4156_ = stack[9].m_obj;
lean_object* v___y_4157_ = stack[10].m_obj;
lean_object* v___y_4158_ = stack[11].m_obj;
lean_object* v___y_4159_ = stack[12].m_obj;
lean_object* v___y_4160_ = stack[13].m_obj;
lean_object* v___y_4161_ = stack[14].m_obj;
lean_object* v_res_4180_;
v_res_4180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4147_, v_as_4148_, v_sz_4149_, v_i_4150_, v_b_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
stack->m_obj
 = v_res_4180_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_____s_4181_, lean_object* v_as_4182_, lean_object* v_sz_4183_, lean_object* v_i_4184_, lean_object* v_b_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
size_t v_sz_boxed_4197_; size_t v_i_boxed_4198_; lean_object* v_res_4199_; 
v_sz_boxed_4197_ = lean_unbox_usize(v_sz_4183_);
lean_dec(v_sz_4183_);
v_i_boxed_4198_ = lean_unbox_usize(v_i_4184_);
lean_dec(v_i_4184_);
v_res_4199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4181_, v_as_4182_, v_sz_boxed_4197_, v_i_boxed_4198_, v_b_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v_as_4182_);
lean_dec(v_____s_4181_);
return v_res_4199_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_init_4200_, lean_object* v_____s_4201_, lean_object* v_n_4202_, lean_object* v_b_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
if (lean_obj_tag(v_n_4202_) == 0)
{
lean_object* v_cs_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; size_t v_sz_4218_; size_t v___x_4219_; lean_object* v___x_4220_; 
v_cs_4215_ = lean_ctor_get(v_n_4202_, 0);
v___x_4216_ = lean_box(0);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4216_);
lean_ctor_set(v___x_4217_, 1, v_b_4203_);
v_sz_4218_ = lean_array_size(v_cs_4215_);
v___x_4219_ = ((size_t)0ULL);
v___x_4220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4200_, v_____s_4201_, v_cs_4215_, v_sz_4218_, v___x_4219_, v___x_4217_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4235_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4235_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4235_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v_fst_4225_; 
v_fst_4225_ = lean_ctor_get(v_a_4221_, 0);
if (lean_obj_tag(v_fst_4225_) == 0)
{
lean_object* v_snd_4226_; lean_object* v___x_4227_; lean_object* v___x_4229_; 
v_snd_4226_ = lean_ctor_get(v_a_4221_, 1);
lean_inc(v_snd_4226_);
lean_dec(v_a_4221_);
v___x_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4227_, 0, v_snd_4226_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v___x_4227_);
v___x_4229_ = v___x_4223_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
else
{
lean_object* v_val_4231_; lean_object* v___x_4233_; 
lean_inc_ref(v_fst_4225_);
lean_dec(v_a_4221_);
v_val_4231_ = lean_ctor_get(v_fst_4225_, 0);
lean_inc(v_val_4231_);
lean_dec_ref_known(v_fst_4225_, 1);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v_val_4231_);
v___x_4233_ = v___x_4223_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_val_4231_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
v_a_4236_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4220_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4220_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
else
{
lean_object* v_vs_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; size_t v_sz_4247_; size_t v___x_4248_; lean_object* v___x_4249_; 
v_vs_4244_ = lean_ctor_get(v_n_4202_, 0);
v___x_4245_ = lean_box(0);
v___x_4246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
lean_ctor_set(v___x_4246_, 1, v_b_4203_);
v_sz_4247_ = lean_array_size(v_vs_4244_);
v___x_4248_ = ((size_t)0ULL);
v___x_4249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4201_, v_vs_4244_, v_sz_4247_, v___x_4248_, v___x_4246_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4264_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4252_ = v___x_4249_;
v_isShared_4253_ = v_isSharedCheck_4264_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4249_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4264_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v_fst_4254_; 
v_fst_4254_ = lean_ctor_get(v_a_4250_, 0);
if (lean_obj_tag(v_fst_4254_) == 0)
{
lean_object* v_snd_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
v_snd_4255_ = lean_ctor_get(v_a_4250_, 1);
lean_inc(v_snd_4255_);
lean_dec(v_a_4250_);
v___x_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4256_, 0, v_snd_4255_);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v___x_4256_);
v___x_4258_ = v___x_4252_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
else
{
lean_object* v_val_4260_; lean_object* v___x_4262_; 
lean_inc_ref(v_fst_4254_);
lean_dec(v_a_4250_);
v_val_4260_ = lean_ctor_get(v_fst_4254_, 0);
lean_inc(v_val_4260_);
lean_dec_ref_known(v_fst_4254_, 1);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v_val_4260_);
v___x_4262_ = v___x_4252_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_val_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
v_a_4265_ = lean_ctor_get(v___x_4249_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4249_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4249_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4200_ = stack[0].m_obj;
lean_object* v_____s_4201_ = stack[1].m_obj;
lean_object* v_n_4202_ = stack[2].m_obj;
lean_object* v_b_4203_ = stack[3].m_obj;
lean_object* v___y_4204_ = stack[4].m_obj;
lean_object* v___y_4205_ = stack[5].m_obj;
lean_object* v___y_4206_ = stack[6].m_obj;
lean_object* v___y_4207_ = stack[7].m_obj;
lean_object* v___y_4208_ = stack[8].m_obj;
lean_object* v___y_4209_ = stack[9].m_obj;
lean_object* v___y_4210_ = stack[10].m_obj;
lean_object* v___y_4211_ = stack[11].m_obj;
lean_object* v___y_4212_ = stack[12].m_obj;
lean_object* v___y_4213_ = stack[13].m_obj;
lean_object* v_res_4273_;
v_res_4273_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4200_, v_____s_4201_, v_n_4202_, v_b_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
stack->m_obj
 = v_res_4273_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_4274_, lean_object* v_____s_4275_, lean_object* v_as_4276_, size_t v_sz_4277_, size_t v_i_4278_, lean_object* v_b_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
uint8_t v___x_4291_; 
v___x_4291_ = lean_usize_dec_lt(v_i_4278_, v_sz_4277_);
if (v___x_4291_ == 0)
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4292_, 0, v_b_4279_);
return v___x_4292_;
}
else
{
lean_object* v_snd_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4327_; 
v_snd_4293_ = lean_ctor_get(v_b_4279_, 1);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_b_4279_);
if (v_isSharedCheck_4327_ == 0)
{
lean_object* v_unused_4328_; 
v_unused_4328_ = lean_ctor_get(v_b_4279_, 0);
lean_dec(v_unused_4328_);
v___x_4295_ = v_b_4279_;
v_isShared_4296_ = v_isSharedCheck_4327_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_snd_4293_);
lean_dec(v_b_4279_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4327_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4297_; lean_object* v_a_4298_; lean_object* v___x_4299_; 
v___x_4297_ = lean_box(0);
v_a_4298_ = lean_array_uget_borrowed(v_as_4276_, v_i_4278_);
lean_inc(v_snd_4293_);
v___x_4299_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4274_, v_____s_4275_, v_a_4298_, v_snd_4293_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4318_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4318_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4318_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
if (lean_obj_tag(v_a_4300_) == 0)
{
lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4304_, 0, v_a_4300_);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4304_);
v___x_4306_ = v___x_4295_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4304_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v_snd_4293_);
v___x_4306_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4308_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v___x_4306_);
v___x_4308_ = v___x_4302_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4306_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; 
lean_del_object(v___x_4302_);
lean_dec(v_snd_4293_);
v_a_4311_ = lean_ctor_get(v_a_4300_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v_a_4300_, 1);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 1, v_a_4311_);
lean_ctor_set(v___x_4295_, 0, v___x_4297_);
v___x_4313_ = v___x_4295_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4297_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v_a_4311_);
v___x_4313_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
size_t v___x_4314_; size_t v___x_4315_; 
v___x_4314_ = ((size_t)1ULL);
v___x_4315_ = lean_usize_add(v_i_4278_, v___x_4314_);
v_i_4278_ = v___x_4315_;
v_b_4279_ = v___x_4313_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_del_object(v___x_4295_);
lean_dec(v_snd_4293_);
v_a_4319_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4299_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4299_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4274_ = stack[0].m_obj;
lean_object* v_____s_4275_ = stack[1].m_obj;
lean_object* v_as_4276_ = stack[2].m_obj;
size_t v_sz_4277_ = stack[3].m_num;
size_t v_i_4278_ = stack[4].m_num;
lean_object* v_b_4279_ = stack[5].m_obj;
lean_object* v___y_4280_ = stack[6].m_obj;
lean_object* v___y_4281_ = stack[7].m_obj;
lean_object* v___y_4282_ = stack[8].m_obj;
lean_object* v___y_4283_ = stack[9].m_obj;
lean_object* v___y_4284_ = stack[10].m_obj;
lean_object* v___y_4285_ = stack[11].m_obj;
lean_object* v___y_4286_ = stack[12].m_obj;
lean_object* v___y_4287_ = stack[13].m_obj;
lean_object* v___y_4288_ = stack[14].m_obj;
lean_object* v___y_4289_ = stack[15].m_obj;
lean_object* v_res_4329_;
v_res_4329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4274_, v_____s_4275_, v_as_4276_, v_sz_4277_, v_i_4278_, v_b_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
stack->m_obj
 = v_res_4329_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_4330_ = _args[0];
lean_object* v_____s_4331_ = _args[1];
lean_object* v_as_4332_ = _args[2];
lean_object* v_sz_4333_ = _args[3];
lean_object* v_i_4334_ = _args[4];
lean_object* v_b_4335_ = _args[5];
lean_object* v___y_4336_ = _args[6];
lean_object* v___y_4337_ = _args[7];
lean_object* v___y_4338_ = _args[8];
lean_object* v___y_4339_ = _args[9];
lean_object* v___y_4340_ = _args[10];
lean_object* v___y_4341_ = _args[11];
lean_object* v___y_4342_ = _args[12];
lean_object* v___y_4343_ = _args[13];
lean_object* v___y_4344_ = _args[14];
lean_object* v___y_4345_ = _args[15];
lean_object* v___y_4346_ = _args[16];
_start:
{
size_t v_sz_boxed_4347_; size_t v_i_boxed_4348_; lean_object* v_res_4349_; 
v_sz_boxed_4347_ = lean_unbox_usize(v_sz_4333_);
lean_dec(v_sz_4333_);
v_i_boxed_4348_ = lean_unbox_usize(v_i_4334_);
lean_dec(v_i_4334_);
v_res_4349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4330_, v_____s_4331_, v_as_4332_, v_sz_boxed_4347_, v_i_boxed_4348_, v_b_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v_as_4332_);
lean_dec(v_____s_4331_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_init_4350_, lean_object* v_____s_4351_, lean_object* v_n_4352_, lean_object* v_b_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4350_, v_____s_4351_, v_n_4352_, v_b_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v_n_4352_);
lean_dec(v_____s_4351_);
return v_res_4365_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(lean_object* v_____s_4366_, lean_object* v_t_4367_, lean_object* v_init_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v_root_4380_; lean_object* v_tail_4381_; lean_object* v___x_4382_; 
v_root_4380_ = lean_ctor_get(v_t_4367_, 0);
v_tail_4381_ = lean_ctor_get(v_t_4367_, 1);
v___x_4382_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4368_, v_____s_4366_, v_root_4380_, v_init_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4419_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4385_ = v___x_4382_;
v_isShared_4386_ = v_isSharedCheck_4419_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4382_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4419_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
if (lean_obj_tag(v_a_4383_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4389_; 
v_a_4387_ = lean_ctor_get(v_a_4383_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v_a_4383_, 1);
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 0, v_a_4387_);
v___x_4389_ = v___x_4385_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4387_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; size_t v_sz_4394_; size_t v___x_4395_; lean_object* v___x_4396_; 
lean_del_object(v___x_4385_);
v_a_4391_ = lean_ctor_get(v_a_4383_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v_a_4383_, 1);
v___x_4392_ = lean_box(0);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
lean_ctor_set(v___x_4393_, 1, v_a_4391_);
v_sz_4394_ = lean_array_size(v_tail_4381_);
v___x_4395_ = ((size_t)0ULL);
v___x_4396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4366_, v_tail_4381_, v_sz_4394_, v___x_4395_, v___x_4393_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4410_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4399_ = v___x_4396_;
v_isShared_4400_ = v_isSharedCheck_4410_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4396_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4410_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v_fst_4401_; 
v_fst_4401_ = lean_ctor_get(v_a_4397_, 0);
if (lean_obj_tag(v_fst_4401_) == 0)
{
lean_object* v_snd_4402_; lean_object* v___x_4404_; 
v_snd_4402_ = lean_ctor_get(v_a_4397_, 1);
lean_inc(v_snd_4402_);
lean_dec(v_a_4397_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v_snd_4402_);
v___x_4404_ = v___x_4399_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_snd_4402_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
else
{
lean_object* v_val_4406_; lean_object* v___x_4408_; 
lean_inc_ref(v_fst_4401_);
lean_dec(v_a_4397_);
v_val_4406_ = lean_ctor_get(v_fst_4401_, 0);
lean_inc(v_val_4406_);
lean_dec_ref_known(v_fst_4401_, 1);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v_val_4406_);
v___x_4408_ = v___x_4399_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_val_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
v_a_4411_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4396_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4396_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
v_a_4420_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4382_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4382_);
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
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____s_4366_ = stack[0].m_obj;
lean_object* v_t_4367_ = stack[1].m_obj;
lean_object* v_init_4368_ = stack[2].m_obj;
lean_object* v___y_4369_ = stack[3].m_obj;
lean_object* v___y_4370_ = stack[4].m_obj;
lean_object* v___y_4371_ = stack[5].m_obj;
lean_object* v___y_4372_ = stack[6].m_obj;
lean_object* v___y_4373_ = stack[7].m_obj;
lean_object* v___y_4374_ = stack[8].m_obj;
lean_object* v___y_4375_ = stack[9].m_obj;
lean_object* v___y_4376_ = stack[10].m_obj;
lean_object* v___y_4377_ = stack[11].m_obj;
lean_object* v___y_4378_ = stack[12].m_obj;
lean_object* v_res_4428_;
v_res_4428_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_____s_4366_, v_t_4367_, v_init_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
stack->m_obj
 = v_res_4428_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_4429_, lean_object* v_t_4430_, lean_object* v_init_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_____s_4429_, v_t_4430_, v_init_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v_t_4430_);
lean_dec(v_____s_4429_);
return v_res_4443_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_4444_, size_t v_sz_4445_, size_t v_i_4446_, lean_object* v_b_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
uint8_t v___x_4459_; 
v___x_4459_ = lean_usize_dec_lt(v_i_4446_, v_sz_4445_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4460_, 0, v_b_4447_);
return v___x_4460_;
}
else
{
lean_object* v_snd_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4485_; 
v_snd_4461_ = lean_ctor_get(v_b_4447_, 1);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_b_4447_);
if (v_isSharedCheck_4485_ == 0)
{
lean_object* v_unused_4486_; 
v_unused_4486_ = lean_ctor_get(v_b_4447_, 0);
lean_dec(v_unused_4486_);
v___x_4463_ = v_b_4447_;
v_isShared_4464_ = v_isSharedCheck_4485_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_snd_4461_);
lean_dec(v_b_4447_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4485_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v_a_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4465_ = lean_box(0);
v_a_4466_ = lean_array_uget_borrowed(v_as_4444_, v_i_4446_);
v___x_4467_ = lean_box(0);
v___x_4468_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4461_, v_a_4466_, v___x_4467_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4472_; 
lean_dec_ref_known(v___x_4468_, 1);
v___x_4469_ = lean_unsigned_to_nat(1u);
v___x_4470_ = lean_nat_add(v_snd_4461_, v___x_4469_);
lean_dec(v_snd_4461_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 1, v___x_4470_);
lean_ctor_set(v___x_4463_, 0, v___x_4465_);
v___x_4472_ = v___x_4463_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v___x_4470_);
v___x_4472_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
size_t v___x_4473_; size_t v___x_4474_; 
v___x_4473_ = ((size_t)1ULL);
v___x_4474_ = lean_usize_add(v_i_4446_, v___x_4473_);
v_i_4446_ = v___x_4474_;
v_b_4447_ = v___x_4472_;
goto _start;
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_del_object(v___x_4463_);
lean_dec(v_snd_4461_);
v_a_4477_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4468_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4468_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4444_ = stack[0].m_obj;
size_t v_sz_4445_ = stack[1].m_num;
size_t v_i_4446_ = stack[2].m_num;
lean_object* v_b_4447_ = stack[3].m_obj;
lean_object* v___y_4448_ = stack[4].m_obj;
lean_object* v___y_4449_ = stack[5].m_obj;
lean_object* v___y_4450_ = stack[6].m_obj;
lean_object* v___y_4451_ = stack[7].m_obj;
lean_object* v___y_4452_ = stack[8].m_obj;
lean_object* v___y_4453_ = stack[9].m_obj;
lean_object* v___y_4454_ = stack[10].m_obj;
lean_object* v___y_4455_ = stack[11].m_obj;
lean_object* v___y_4456_ = stack[12].m_obj;
lean_object* v___y_4457_ = stack[13].m_obj;
lean_object* v_res_4487_;
v_res_4487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4444_, v_sz_4445_, v_i_4446_, v_b_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
stack->m_obj
 = v_res_4487_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_4488_, lean_object* v_sz_4489_, lean_object* v_i_4490_, lean_object* v_b_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
size_t v_sz_boxed_4503_; size_t v_i_boxed_4504_; lean_object* v_res_4505_; 
v_sz_boxed_4503_ = lean_unbox_usize(v_sz_4489_);
lean_dec(v_sz_4489_);
v_i_boxed_4504_ = lean_unbox_usize(v_i_4490_);
lean_dec(v_i_4490_);
v_res_4505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4488_, v_sz_boxed_4503_, v_i_boxed_4504_, v_b_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
lean_dec(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v_as_4488_);
return v_res_4505_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_4506_, size_t v_sz_4507_, size_t v_i_4508_, lean_object* v_b_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v___x_4521_; 
v___x_4521_ = lean_usize_dec_lt(v_i_4508_, v_sz_4507_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; 
v___x_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4522_, 0, v_b_4509_);
return v___x_4522_;
}
else
{
lean_object* v_snd_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4547_; 
v_snd_4523_ = lean_ctor_get(v_b_4509_, 1);
v_isSharedCheck_4547_ = !lean_is_exclusive(v_b_4509_);
if (v_isSharedCheck_4547_ == 0)
{
lean_object* v_unused_4548_; 
v_unused_4548_ = lean_ctor_get(v_b_4509_, 0);
lean_dec(v_unused_4548_);
v___x_4525_ = v_b_4509_;
v_isShared_4526_ = v_isSharedCheck_4547_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_snd_4523_);
lean_dec(v_b_4509_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4547_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4527_; lean_object* v_a_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4527_ = lean_box(0);
v_a_4528_ = lean_array_uget_borrowed(v_as_4506_, v_i_4508_);
v___x_4529_ = lean_box(0);
v___x_4530_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4523_, v_a_4528_, v___x_4529_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4534_; 
lean_dec_ref_known(v___x_4530_, 1);
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4532_ = lean_nat_add(v_snd_4523_, v___x_4531_);
lean_dec(v_snd_4523_);
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 1, v___x_4532_);
lean_ctor_set(v___x_4525_, 0, v___x_4527_);
v___x_4534_ = v___x_4525_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4527_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v___x_4532_);
v___x_4534_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
size_t v___x_4535_; size_t v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = ((size_t)1ULL);
v___x_4536_ = lean_usize_add(v_i_4508_, v___x_4535_);
v___x_4537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4506_, v_sz_4507_, v___x_4536_, v___x_4534_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
return v___x_4537_;
}
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
lean_del_object(v___x_4525_);
lean_dec(v_snd_4523_);
v_a_4539_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4541_ = v___x_4530_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4530_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4506_ = stack[0].m_obj;
size_t v_sz_4507_ = stack[1].m_num;
size_t v_i_4508_ = stack[2].m_num;
lean_object* v_b_4509_ = stack[3].m_obj;
lean_object* v___y_4510_ = stack[4].m_obj;
lean_object* v___y_4511_ = stack[5].m_obj;
lean_object* v___y_4512_ = stack[6].m_obj;
lean_object* v___y_4513_ = stack[7].m_obj;
lean_object* v___y_4514_ = stack[8].m_obj;
lean_object* v___y_4515_ = stack[9].m_obj;
lean_object* v___y_4516_ = stack[10].m_obj;
lean_object* v___y_4517_ = stack[11].m_obj;
lean_object* v___y_4518_ = stack[12].m_obj;
lean_object* v___y_4519_ = stack[13].m_obj;
lean_object* v_res_4549_;
v_res_4549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_4506_, v_sz_4507_, v_i_4508_, v_b_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
stack->m_obj
 = v_res_4549_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_4550_, lean_object* v_sz_4551_, lean_object* v_i_4552_, lean_object* v_b_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
size_t v_sz_boxed_4565_; size_t v_i_boxed_4566_; lean_object* v_res_4567_; 
v_sz_boxed_4565_ = lean_unbox_usize(v_sz_4551_);
lean_dec(v_sz_4551_);
v_i_boxed_4566_ = lean_unbox_usize(v_i_4552_);
lean_dec(v_i_4552_);
v_res_4567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_4550_, v_sz_boxed_4565_, v_i_boxed_4566_, v_b_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v_as_4550_);
return v_res_4567_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_init_4568_, lean_object* v_n_4569_, lean_object* v_b_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
if (lean_obj_tag(v_n_4569_) == 0)
{
lean_object* v_cs_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; size_t v_sz_4585_; size_t v___x_4586_; lean_object* v___x_4587_; 
v_cs_4582_ = lean_ctor_get(v_n_4569_, 0);
v___x_4583_ = lean_box(0);
v___x_4584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
lean_ctor_set(v___x_4584_, 1, v_b_4570_);
v_sz_4585_ = lean_array_size(v_cs_4582_);
v___x_4586_ = ((size_t)0ULL);
v___x_4587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4568_, v_cs_4582_, v_sz_4585_, v___x_4586_, v___x_4584_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4602_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4590_ = v___x_4587_;
v_isShared_4591_ = v_isSharedCheck_4602_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4587_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4602_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v_fst_4592_; 
v_fst_4592_ = lean_ctor_get(v_a_4588_, 0);
if (lean_obj_tag(v_fst_4592_) == 0)
{
lean_object* v_snd_4593_; lean_object* v___x_4594_; lean_object* v___x_4596_; 
v_snd_4593_ = lean_ctor_get(v_a_4588_, 1);
lean_inc(v_snd_4593_);
lean_dec(v_a_4588_);
v___x_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4594_, 0, v_snd_4593_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v___x_4594_);
v___x_4596_ = v___x_4590_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4594_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
else
{
lean_object* v_val_4598_; lean_object* v___x_4600_; 
lean_inc_ref(v_fst_4592_);
lean_dec(v_a_4588_);
v_val_4598_ = lean_ctor_get(v_fst_4592_, 0);
lean_inc(v_val_4598_);
lean_dec_ref_known(v_fst_4592_, 1);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v_val_4598_);
v___x_4600_ = v___x_4590_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_val_4598_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
v_a_4603_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4587_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4587_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
else
{
lean_object* v_vs_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; size_t v_sz_4614_; size_t v___x_4615_; lean_object* v___x_4616_; 
v_vs_4611_ = lean_ctor_get(v_n_4569_, 0);
v___x_4612_ = lean_box(0);
v___x_4613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4612_);
lean_ctor_set(v___x_4613_, 1, v_b_4570_);
v_sz_4614_ = lean_array_size(v_vs_4611_);
v___x_4615_ = ((size_t)0ULL);
v___x_4616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_4611_, v_sz_4614_, v___x_4615_, v___x_4613_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4631_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4619_ = v___x_4616_;
v_isShared_4620_ = v_isSharedCheck_4631_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4616_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4631_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v_fst_4621_; 
v_fst_4621_ = lean_ctor_get(v_a_4617_, 0);
if (lean_obj_tag(v_fst_4621_) == 0)
{
lean_object* v_snd_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v_snd_4622_ = lean_ctor_get(v_a_4617_, 1);
lean_inc(v_snd_4622_);
lean_dec(v_a_4617_);
v___x_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4623_, 0, v_snd_4622_);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 0, v___x_4623_);
v___x_4625_ = v___x_4619_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
else
{
lean_object* v_val_4627_; lean_object* v___x_4629_; 
lean_inc_ref(v_fst_4621_);
lean_dec(v_a_4617_);
v_val_4627_ = lean_ctor_get(v_fst_4621_, 0);
lean_inc(v_val_4627_);
lean_dec_ref_known(v_fst_4621_, 1);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 0, v_val_4627_);
v___x_4629_ = v___x_4619_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_val_4627_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
v_a_4632_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4616_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4616_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4568_ = stack[0].m_obj;
lean_object* v_n_4569_ = stack[1].m_obj;
lean_object* v_b_4570_ = stack[2].m_obj;
lean_object* v___y_4571_ = stack[3].m_obj;
lean_object* v___y_4572_ = stack[4].m_obj;
lean_object* v___y_4573_ = stack[5].m_obj;
lean_object* v___y_4574_ = stack[6].m_obj;
lean_object* v___y_4575_ = stack[7].m_obj;
lean_object* v___y_4576_ = stack[8].m_obj;
lean_object* v___y_4577_ = stack[9].m_obj;
lean_object* v___y_4578_ = stack[10].m_obj;
lean_object* v___y_4579_ = stack[11].m_obj;
lean_object* v___y_4580_ = stack[12].m_obj;
lean_object* v_res_4640_;
v_res_4640_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4568_, v_n_4569_, v_b_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
stack->m_obj
 = v_res_4640_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_init_4641_, lean_object* v_as_4642_, size_t v_sz_4643_, size_t v_i_4644_, lean_object* v_b_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
uint8_t v___x_4657_; 
v___x_4657_ = lean_usize_dec_lt(v_i_4644_, v_sz_4643_);
if (v___x_4657_ == 0)
{
lean_object* v___x_4658_; 
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v_b_4645_);
return v___x_4658_;
}
else
{
lean_object* v_snd_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4693_; 
v_snd_4659_ = lean_ctor_get(v_b_4645_, 1);
v_isSharedCheck_4693_ = !lean_is_exclusive(v_b_4645_);
if (v_isSharedCheck_4693_ == 0)
{
lean_object* v_unused_4694_; 
v_unused_4694_ = lean_ctor_get(v_b_4645_, 0);
lean_dec(v_unused_4694_);
v___x_4661_ = v_b_4645_;
v_isShared_4662_ = v_isSharedCheck_4693_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_snd_4659_);
lean_dec(v_b_4645_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4693_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4663_; lean_object* v_a_4664_; lean_object* v___x_4665_; 
v___x_4663_ = lean_box(0);
v_a_4664_ = lean_array_uget_borrowed(v_as_4642_, v_i_4644_);
lean_inc(v_snd_4659_);
v___x_4665_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4641_, v_a_4664_, v_snd_4659_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4684_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4684_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4684_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
if (lean_obj_tag(v_a_4666_) == 0)
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4670_, 0, v_a_4666_);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4670_);
v___x_4672_ = v___x_4661_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_snd_4659_);
v___x_4672_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4674_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v___x_4672_);
v___x_4674_ = v___x_4668_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4672_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; 
lean_del_object(v___x_4668_);
lean_dec(v_snd_4659_);
v_a_4677_ = lean_ctor_get(v_a_4666_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v_a_4666_, 1);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 1, v_a_4677_);
lean_ctor_set(v___x_4661_, 0, v___x_4663_);
v___x_4679_ = v___x_4661_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4663_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v_a_4677_);
v___x_4679_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
size_t v___x_4680_; size_t v___x_4681_; 
v___x_4680_ = ((size_t)1ULL);
v___x_4681_ = lean_usize_add(v_i_4644_, v___x_4680_);
v_i_4644_ = v___x_4681_;
v_b_4645_ = v___x_4679_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4692_; 
lean_del_object(v___x_4661_);
lean_dec(v_snd_4659_);
v_a_4685_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4687_ = v___x_4665_;
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4665_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
if (v_isShared_4688_ == 0)
{
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4685_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4641_ = stack[0].m_obj;
lean_object* v_as_4642_ = stack[1].m_obj;
size_t v_sz_4643_ = stack[2].m_num;
size_t v_i_4644_ = stack[3].m_num;
lean_object* v_b_4645_ = stack[4].m_obj;
lean_object* v___y_4646_ = stack[5].m_obj;
lean_object* v___y_4647_ = stack[6].m_obj;
lean_object* v___y_4648_ = stack[7].m_obj;
lean_object* v___y_4649_ = stack[8].m_obj;
lean_object* v___y_4650_ = stack[9].m_obj;
lean_object* v___y_4651_ = stack[10].m_obj;
lean_object* v___y_4652_ = stack[11].m_obj;
lean_object* v___y_4653_ = stack[12].m_obj;
lean_object* v___y_4654_ = stack[13].m_obj;
lean_object* v___y_4655_ = stack[14].m_obj;
lean_object* v_res_4695_;
v_res_4695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4641_, v_as_4642_, v_sz_4643_, v_i_4644_, v_b_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
stack->m_obj
 = v_res_4695_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object* v_init_4696_, lean_object* v_as_4697_, lean_object* v_sz_4698_, lean_object* v_i_4699_, lean_object* v_b_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
size_t v_sz_boxed_4712_; size_t v_i_boxed_4713_; lean_object* v_res_4714_; 
v_sz_boxed_4712_ = lean_unbox_usize(v_sz_4698_);
lean_dec(v_sz_4698_);
v_i_boxed_4713_ = lean_unbox_usize(v_i_4699_);
lean_dec(v_i_4699_);
v_res_4714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4696_, v_as_4697_, v_sz_boxed_4712_, v_i_boxed_4713_, v_b_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v_as_4697_);
lean_dec(v_init_4696_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_init_4715_, lean_object* v_n_4716_, lean_object* v_b_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4715_, v_n_4716_, v_b_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v_n_4716_);
lean_dec(v_init_4715_);
return v_res_4729_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_4730_, size_t v_sz_4731_, size_t v_i_4732_, lean_object* v_b_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_){
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
lean_object* v___x_4751_; lean_object* v_a_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4751_ = lean_box(0);
v_a_4752_ = lean_array_uget_borrowed(v_as_4730_, v_i_4732_);
v___x_4753_ = lean_box(0);
v___x_4754_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4747_, v_a_4752_, v___x_4753_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
lean_dec_ref_known(v___x_4754_, 1);
v___x_4755_ = lean_unsigned_to_nat(1u);
v___x_4756_ = lean_nat_add(v_snd_4747_, v___x_4755_);
lean_dec(v_snd_4747_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 1, v___x_4756_);
lean_ctor_set(v___x_4749_, 0, v___x_4751_);
v___x_4758_ = v___x_4749_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
size_t v___x_4759_; size_t v___x_4760_; 
v___x_4759_ = ((size_t)1ULL);
v___x_4760_ = lean_usize_add(v_i_4732_, v___x_4759_);
v_i_4732_ = v___x_4760_;
v_b_4733_ = v___x_4758_;
goto _start;
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_del_object(v___x_4749_);
lean_dec(v_snd_4747_);
v_a_4763_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4754_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4754_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4730_ = stack[0].m_obj;
size_t v_sz_4731_ = stack[1].m_num;
size_t v_i_4732_ = stack[2].m_num;
lean_object* v_b_4733_ = stack[3].m_obj;
lean_object* v___y_4734_ = stack[4].m_obj;
lean_object* v___y_4735_ = stack[5].m_obj;
lean_object* v___y_4736_ = stack[6].m_obj;
lean_object* v___y_4737_ = stack[7].m_obj;
lean_object* v___y_4738_ = stack[8].m_obj;
lean_object* v___y_4739_ = stack[9].m_obj;
lean_object* v___y_4740_ = stack[10].m_obj;
lean_object* v___y_4741_ = stack[11].m_obj;
lean_object* v___y_4742_ = stack[12].m_obj;
lean_object* v___y_4743_ = stack[13].m_obj;
lean_object* v_res_4773_;
v_res_4773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4730_, v_sz_4731_, v_i_4732_, v_b_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
stack->m_obj
 = v_res_4773_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_4774_, lean_object* v_sz_4775_, lean_object* v_i_4776_, lean_object* v_b_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
size_t v_sz_boxed_4789_; size_t v_i_boxed_4790_; lean_object* v_res_4791_; 
v_sz_boxed_4789_ = lean_unbox_usize(v_sz_4775_);
lean_dec(v_sz_4775_);
v_i_boxed_4790_ = lean_unbox_usize(v_i_4776_);
lean_dec(v_i_4776_);
v_res_4791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4774_, v_sz_boxed_4789_, v_i_boxed_4790_, v_b_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
lean_dec(v___y_4787_);
lean_dec_ref(v___y_4786_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v_as_4774_);
return v_res_4791_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_4792_, size_t v_sz_4793_, size_t v_i_4794_, lean_object* v_b_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
uint8_t v___x_4807_; 
v___x_4807_ = lean_usize_dec_lt(v_i_4794_, v_sz_4793_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; 
v___x_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4808_, 0, v_b_4795_);
return v___x_4808_;
}
else
{
lean_object* v_snd_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4833_; 
v_snd_4809_ = lean_ctor_get(v_b_4795_, 1);
v_isSharedCheck_4833_ = !lean_is_exclusive(v_b_4795_);
if (v_isSharedCheck_4833_ == 0)
{
lean_object* v_unused_4834_; 
v_unused_4834_ = lean_ctor_get(v_b_4795_, 0);
lean_dec(v_unused_4834_);
v___x_4811_ = v_b_4795_;
v_isShared_4812_ = v_isSharedCheck_4833_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_snd_4809_);
lean_dec(v_b_4795_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4833_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4813_; lean_object* v_a_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4813_ = lean_box(0);
v_a_4814_ = lean_array_uget_borrowed(v_as_4792_, v_i_4794_);
v___x_4815_ = lean_box(0);
v___x_4816_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4809_, v_a_4814_, v___x_4815_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4820_; 
lean_dec_ref_known(v___x_4816_, 1);
v___x_4817_ = lean_unsigned_to_nat(1u);
v___x_4818_ = lean_nat_add(v_snd_4809_, v___x_4817_);
lean_dec(v_snd_4809_);
if (v_isShared_4812_ == 0)
{
lean_ctor_set(v___x_4811_, 1, v___x_4818_);
lean_ctor_set(v___x_4811_, 0, v___x_4813_);
v___x_4820_ = v___x_4811_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4813_);
lean_ctor_set(v_reuseFailAlloc_4824_, 1, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
size_t v___x_4821_; size_t v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = ((size_t)1ULL);
v___x_4822_ = lean_usize_add(v_i_4794_, v___x_4821_);
v___x_4823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4792_, v_sz_4793_, v___x_4822_, v___x_4820_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
return v___x_4823_;
}
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
lean_del_object(v___x_4811_);
lean_dec(v_snd_4809_);
v_a_4825_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4827_ = v___x_4816_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4816_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4792_ = stack[0].m_obj;
size_t v_sz_4793_ = stack[1].m_num;
size_t v_i_4794_ = stack[2].m_num;
lean_object* v_b_4795_ = stack[3].m_obj;
lean_object* v___y_4796_ = stack[4].m_obj;
lean_object* v___y_4797_ = stack[5].m_obj;
lean_object* v___y_4798_ = stack[6].m_obj;
lean_object* v___y_4799_ = stack[7].m_obj;
lean_object* v___y_4800_ = stack[8].m_obj;
lean_object* v___y_4801_ = stack[9].m_obj;
lean_object* v___y_4802_ = stack[10].m_obj;
lean_object* v___y_4803_ = stack[11].m_obj;
lean_object* v___y_4804_ = stack[12].m_obj;
lean_object* v___y_4805_ = stack[13].m_obj;
lean_object* v_res_4835_;
v_res_4835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_as_4792_, v_sz_4793_, v_i_4794_, v_b_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
stack->m_obj
 = v_res_4835_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_4836_, lean_object* v_sz_4837_, lean_object* v_i_4838_, lean_object* v_b_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
size_t v_sz_boxed_4851_; size_t v_i_boxed_4852_; lean_object* v_res_4853_; 
v_sz_boxed_4851_ = lean_unbox_usize(v_sz_4837_);
lean_dec(v_sz_4837_);
v_i_boxed_4852_ = lean_unbox_usize(v_i_4838_);
lean_dec(v_i_4838_);
v_res_4853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_as_4836_, v_sz_boxed_4851_, v_i_boxed_4852_, v_b_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec(v___y_4840_);
lean_dec_ref(v_as_4836_);
return v_res_4853_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(lean_object* v_t_4854_, lean_object* v_init_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v_root_4867_; lean_object* v_tail_4868_; lean_object* v___x_4869_; 
v_root_4867_ = lean_ctor_get(v_t_4854_, 0);
v_tail_4868_ = lean_ctor_get(v_t_4854_, 1);
lean_inc(v_init_4855_);
v___x_4869_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4855_, v_root_4867_, v_init_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
lean_dec(v_init_4855_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4906_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4872_ = v___x_4869_;
v_isShared_4873_ = v_isSharedCheck_4906_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4869_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4906_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
if (lean_obj_tag(v_a_4870_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; 
v_a_4874_ = lean_ctor_get(v_a_4870_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v_a_4870_, 1);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 0, v_a_4874_);
v___x_4876_ = v___x_4872_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4874_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; size_t v_sz_4881_; size_t v___x_4882_; lean_object* v___x_4883_; 
lean_del_object(v___x_4872_);
v_a_4878_ = lean_ctor_get(v_a_4870_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v_a_4870_, 1);
v___x_4879_ = lean_box(0);
v___x_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4879_);
lean_ctor_set(v___x_4880_, 1, v_a_4878_);
v_sz_4881_ = lean_array_size(v_tail_4868_);
v___x_4882_ = ((size_t)0ULL);
v___x_4883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_tail_4868_, v_sz_4881_, v___x_4882_, v___x_4880_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4897_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4886_ = v___x_4883_;
v_isShared_4887_ = v_isSharedCheck_4897_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4883_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4897_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v_fst_4888_; 
v_fst_4888_ = lean_ctor_get(v_a_4884_, 0);
if (lean_obj_tag(v_fst_4888_) == 0)
{
lean_object* v_snd_4889_; lean_object* v___x_4891_; 
v_snd_4889_ = lean_ctor_get(v_a_4884_, 1);
lean_inc(v_snd_4889_);
lean_dec(v_a_4884_);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 0, v_snd_4889_);
v___x_4891_ = v___x_4886_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_snd_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
else
{
lean_object* v_val_4893_; lean_object* v___x_4895_; 
lean_inc_ref(v_fst_4888_);
lean_dec(v_a_4884_);
v_val_4893_ = lean_ctor_get(v_fst_4888_, 0);
lean_inc(v_val_4893_);
lean_dec_ref_known(v_fst_4888_, 1);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 0, v_val_4893_);
v___x_4895_ = v___x_4886_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_val_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4905_; 
v_a_4898_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4900_ = v___x_4883_;
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4883_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
}
}
}
else
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4914_; 
v_a_4907_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4909_ = v___x_4869_;
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4869_);
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
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_4854_ = stack[0].m_obj;
lean_object* v_init_4855_ = stack[1].m_obj;
lean_object* v___y_4856_ = stack[2].m_obj;
lean_object* v___y_4857_ = stack[3].m_obj;
lean_object* v___y_4858_ = stack[4].m_obj;
lean_object* v___y_4859_ = stack[5].m_obj;
lean_object* v___y_4860_ = stack[6].m_obj;
lean_object* v___y_4861_ = stack[7].m_obj;
lean_object* v___y_4862_ = stack[8].m_obj;
lean_object* v___y_4863_ = stack[9].m_obj;
lean_object* v___y_4864_ = stack[10].m_obj;
lean_object* v___y_4865_ = stack[11].m_obj;
lean_object* v_res_4915_;
v_res_4915_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_t_4854_, v_init_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
stack->m_obj
 = v_res_4915_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_4916_, lean_object* v_init_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_t_4916_, v_init_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
lean_dec(v___y_4919_);
lean_dec(v___y_4918_);
lean_dec_ref(v_t_4916_);
return v_res_4929_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4932_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1));
v___x_4933_ = lean_unsigned_to_nat(2u);
v___x_4934_ = lean_unsigned_to_nat(103u);
v___x_4935_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0));
v___x_4936_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_4937_ = l_mkPanicMessageWithDecl(v___x_4936_, v___x_4935_, v___x_4934_, v___x_4933_, v___x_4932_);
return v___x_4937_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4938_, v_a_4946_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v_vars_4951_; lean_object* v_diseqs_4952_; lean_object* v_size_4953_; lean_object* v_size_4954_; uint8_t v___x_4955_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___x_4949_, 1);
v_vars_4951_ = lean_ctor_get(v_a_4950_, 0);
lean_inc_ref(v_vars_4951_);
v_diseqs_4952_ = lean_ctor_get(v_a_4950_, 8);
lean_inc_ref(v_diseqs_4952_);
lean_dec(v_a_4950_);
v_size_4953_ = lean_ctor_get(v_vars_4951_, 2);
lean_inc(v_size_4953_);
lean_dec_ref(v_vars_4951_);
v_size_4954_ = lean_ctor_get(v_diseqs_4952_, 2);
v___x_4955_ = lean_nat_dec_eq(v_size_4953_, v_size_4954_);
lean_dec(v_size_4953_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
lean_dec_ref(v_diseqs_4952_);
v___x_4956_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2);
v___x_4957_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_4956_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_);
return v___x_4957_;
}
else
{
lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4958_ = lean_unsigned_to_nat(0u);
v___x_4959_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_diseqs_4952_, v___x_4958_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_);
lean_dec_ref(v_diseqs_4952_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4967_; 
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4967_ == 0)
{
lean_object* v_unused_4968_; 
v_unused_4968_ = lean_ctor_get(v___x_4959_, 0);
lean_dec(v_unused_4968_);
v___x_4961_ = v___x_4959_;
v_isShared_4962_ = v_isSharedCheck_4967_;
goto v_resetjp_4960_;
}
else
{
lean_dec(v___x_4959_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4967_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4963_; lean_object* v___x_4965_; 
v___x_4963_ = lean_box(0);
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 0, v___x_4963_);
v___x_4965_ = v___x_4961_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4963_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
v_a_4969_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4959_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4959_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
v_a_4977_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4949_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4949_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4938_ = stack[0].m_obj;
lean_object* v_a_4939_ = stack[1].m_obj;
lean_object* v_a_4940_ = stack[2].m_obj;
lean_object* v_a_4941_ = stack[3].m_obj;
lean_object* v_a_4942_ = stack[4].m_obj;
lean_object* v_a_4943_ = stack[5].m_obj;
lean_object* v_a_4944_ = stack[6].m_obj;
lean_object* v_a_4945_ = stack[7].m_obj;
lean_object* v_a_4946_ = stack[8].m_obj;
lean_object* v_a_4947_ = stack[9].m_obj;
lean_object* v_res_4985_;
v_res_4985_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_);
stack->m_obj
 = v_res_4985_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___boxed(lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
lean_dec(v_a_4987_);
lean_dec(v_a_4986_);
return v_res_4997_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v___x_5009_; 
v___x_5009_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v___x_5010_; 
lean_dec_ref_known(v___x_5009_, 1);
v___x_5010_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v___x_5011_; 
lean_dec_ref_known(v___x_5010_, 1);
v___x_5011_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v___x_5012_; 
lean_dec_ref_known(v___x_5011_, 1);
v___x_5012_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v___x_5013_; 
lean_dec_ref_known(v___x_5012_, 1);
v___x_5013_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v___x_5014_; 
lean_dec_ref_known(v___x_5013_, 1);
v___x_5014_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_object* v___x_5015_; 
lean_dec_ref_known(v___x_5014_, 1);
v___x_5015_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
return v___x_5015_;
}
else
{
return v___x_5014_;
}
}
else
{
return v___x_5013_;
}
}
else
{
return v___x_5012_;
}
}
else
{
return v___x_5011_;
}
}
else
{
return v___x_5010_;
}
}
else
{
return v___x_5009_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4998_ = stack[0].m_obj;
lean_object* v_a_4999_ = stack[1].m_obj;
lean_object* v_a_5000_ = stack[2].m_obj;
lean_object* v_a_5001_ = stack[3].m_obj;
lean_object* v_a_5002_ = stack[4].m_obj;
lean_object* v_a_5003_ = stack[5].m_obj;
lean_object* v_a_5004_ = stack[6].m_obj;
lean_object* v_a_5005_ = stack[7].m_obj;
lean_object* v_a_5006_ = stack[8].m_obj;
lean_object* v_a_5007_ = stack[9].m_obj;
lean_object* v_res_5016_;
v_res_5016_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
stack->m_obj
 = v_res_5016_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
lean_dec(v_a_5024_);
lean_dec_ref(v_a_5023_);
lean_dec(v_a_5022_);
lean_dec_ref(v_a_5021_);
lean_dec(v_a_5020_);
lean_dec_ref(v_a_5019_);
lean_dec(v_a_5018_);
lean_dec(v_a_5017_);
return v_res_5028_;
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
