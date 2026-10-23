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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: c.p.isSorted\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: c.p.checkCoeffs\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "assertion violation: s.elimStack.contains x\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "assertion violation: c.p.coeff x != 0\n    "};
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
v___x_14_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(lean_object* v_msg_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_1290__overap_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_1290__overap_28_ = lean_panic_fn_borrowed(v___x_27_, v_msg_15_);
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
v___x_29_ = lean_apply_11(v___x_1290__overap_28_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, lean_box(0));
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_3860__overap_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_3860__overap_308_ = lean_panic_fn_borrowed(v___x_307_, v_msg_295_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
lean_inc(v___y_297_);
lean_inc(v___y_296_);
v___x_309_ = lean_apply_11(v___x_3860__overap_308_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___boxed(lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v_msg_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec(v___y_311_);
return v_res_322_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1));
v___x_326_ = lean_unsigned_to_nat(6u);
v___x_327_ = lean_unsigned_to_nat(49u);
v___x_328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_329_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_330_ = l_mkPanicMessageWithDecl(v___x_329_, v___x_328_, v___x_327_, v___x_326_, v___x_325_);
return v___x_330_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_331_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_332_ = lean_unsigned_to_nat(30u);
v___x_333_ = lean_unsigned_to_nat(48u);
v___x_334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_335_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_336_ = l_mkPanicMessageWithDecl(v___x_335_, v___x_334_, v___x_333_, v___x_332_, v___x_331_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object* v_____s_337_, uint8_t v_isLower_338_, lean_object* v_as_339_, size_t v_sz_340_, size_t v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = lean_usize_dec_lt(v_i_341_, v_sz_340_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v_b_342_);
return v___x_355_;
}
else
{
lean_object* v_snd_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_430_; 
v_snd_356_ = lean_ctor_get(v_b_342_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_b_342_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_b_342_, 0);
lean_dec(v_unused_431_);
v___x_358_ = v_b_342_;
v_isShared_359_ = v_isSharedCheck_430_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snd_356_);
lean_dec(v_b_342_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_430_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_a_360_; lean_object* v_p_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_428_; 
v_a_360_ = lean_array_uget(v_as_339_, v_i_341_);
v_p_361_ = lean_ctor_get(v_a_360_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v_a_360_, 1);
lean_dec(v_unused_429_);
v___x_363_ = v_a_360_;
v_isShared_364_ = v_isSharedCheck_428_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_p_361_);
lean_dec(v_a_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_428_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v_a_367_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_365_ = lean_box(0);
v___x_374_ = lean_box(0);
v___x_375_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_361_, v_____s_337_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_dec_ref_known(v___x_375_, 1);
if (lean_obj_tag(v_p_361_) == 1)
{
lean_object* v_k_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_k_407_ = lean_ctor_get(v_p_361_, 0);
lean_inc(v_k_407_);
lean_dec_ref_known(v_p_361_, 3);
v___x_408_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_409_ = lean_int_dec_lt(v_k_407_, v___x_408_);
lean_dec(v_k_407_);
if (v___x_409_ == 0)
{
if (v_isLower_338_ == 0)
{
lean_del_object(v___x_363_);
lean_dec(v_snd_356_);
v_a_367_ = v___x_374_;
goto v___jp_366_;
}
else
{
goto v___jp_376_;
}
}
else
{
if (v_isLower_338_ == 0)
{
goto v___jp_376_;
}
else
{
lean_del_object(v___x_363_);
lean_dec(v_snd_356_);
v_a_367_ = v___x_374_;
goto v___jp_366_;
}
}
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_del_object(v___x_363_);
lean_dec_ref(v_p_361_);
lean_dec(v_snd_356_);
v___x_410_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_411_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_410_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_dec_ref_known(v___x_411_, 1);
v_a_367_ = v___x_374_;
goto v___jp_366_;
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_del_object(v___x_358_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
v___jp_376_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_378_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_377_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
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
lean_del_object(v___x_358_);
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
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v_snd_356_);
lean_ctor_set(v___x_363_, 0, v___x_388_);
v___x_390_ = v___x_363_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_snd_356_);
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
lean_del_object(v___x_363_);
lean_dec(v_snd_356_);
v_a_397_ = lean_ctor_get(v_a_379_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v_a_379_, 1);
v_a_367_ = v_a_397_;
goto v___jp_366_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_del_object(v___x_363_);
lean_del_object(v___x_358_);
lean_dec(v_snd_356_);
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
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_del_object(v___x_363_);
lean_dec_ref(v_p_361_);
lean_del_object(v___x_358_);
lean_dec(v_snd_356_);
v_a_420_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_375_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_375_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
v___jp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v_a_367_);
lean_ctor_set(v___x_358_, 0, v___x_365_);
v___x_369_ = v___x_358_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_a_367_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
size_t v___x_370_; size_t v___x_371_; 
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_341_, v___x_370_);
v_i_341_ = v___x_371_;
v_b_342_ = v___x_369_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_____s_432_ = _args[0];
lean_object* v_isLower_433_ = _args[1];
lean_object* v_as_434_ = _args[2];
lean_object* v_sz_435_ = _args[3];
lean_object* v_i_436_ = _args[4];
lean_object* v_b_437_ = _args[5];
lean_object* v___y_438_ = _args[6];
lean_object* v___y_439_ = _args[7];
lean_object* v___y_440_ = _args[8];
lean_object* v___y_441_ = _args[9];
lean_object* v___y_442_ = _args[10];
lean_object* v___y_443_ = _args[11];
lean_object* v___y_444_ = _args[12];
lean_object* v___y_445_ = _args[13];
lean_object* v___y_446_ = _args[14];
lean_object* v___y_447_ = _args[15];
lean_object* v___y_448_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_449_; size_t v_sz_boxed_450_; size_t v_i_boxed_451_; lean_object* v_res_452_; 
v_isLower_boxed_449_ = lean_unbox(v_isLower_433_);
v_sz_boxed_450_ = lean_unbox_usize(v_sz_435_);
lean_dec(v_sz_435_);
v_i_boxed_451_ = lean_unbox_usize(v_i_436_);
lean_dec(v_i_436_);
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_432_, v_isLower_boxed_449_, v_as_434_, v_sz_boxed_450_, v_i_boxed_451_, v_b_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v_as_434_);
lean_dec(v_____s_432_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(lean_object* v_____s_453_, uint8_t v_isLower_454_, lean_object* v_as_455_, size_t v_sz_456_, size_t v_i_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = lean_usize_dec_lt(v_i_457_, v_sz_456_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_b_458_);
return v___x_471_;
}
else
{
lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_546_; 
v_snd_472_ = lean_ctor_get(v_b_458_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_b_458_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v_b_458_, 0);
lean_dec(v_unused_547_);
v___x_474_ = v_b_458_;
v_isShared_475_ = v_isSharedCheck_546_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_dec(v_b_458_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_546_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v_a_476_; lean_object* v_p_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_544_; 
v_a_476_ = lean_array_uget(v_as_455_, v_i_457_);
v_p_477_ = lean_ctor_get(v_a_476_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_a_476_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_a_476_, 1);
lean_dec(v_unused_545_);
v___x_479_ = v_a_476_;
v_isShared_480_ = v_isSharedCheck_544_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_p_477_);
lean_dec(v_a_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_544_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_a_484_; lean_object* v___x_491_; 
v___x_481_ = lean_box(0);
v___x_482_ = lean_box(0);
v___x_491_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_477_, v_____s_453_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_dec_ref_known(v___x_491_, 1);
if (lean_obj_tag(v_p_477_) == 1)
{
lean_object* v_k_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_k_523_ = lean_ctor_get(v_p_477_, 0);
lean_inc(v_k_523_);
lean_dec_ref_known(v_p_477_, 3);
v___x_524_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_525_ = lean_int_dec_lt(v_k_523_, v___x_524_);
lean_dec(v_k_523_);
if (v___x_525_ == 0)
{
if (v_isLower_454_ == 0)
{
lean_del_object(v___x_479_);
lean_dec(v_snd_472_);
v_a_484_ = v___x_481_;
goto v___jp_483_;
}
else
{
goto v___jp_492_;
}
}
else
{
if (v_isLower_454_ == 0)
{
goto v___jp_492_;
}
else
{
lean_del_object(v___x_479_);
lean_dec(v_snd_472_);
v_a_484_ = v___x_481_;
goto v___jp_483_;
}
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_del_object(v___x_479_);
lean_dec_ref(v_p_477_);
lean_dec(v_snd_472_);
v___x_526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_527_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_526_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec_ref_known(v___x_527_, 1);
v_a_484_ = v___x_481_;
goto v___jp_483_;
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_del_object(v___x_474_);
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
v___jp_492_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_494_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_493_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_514_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_514_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
if (lean_obj_tag(v_a_495_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_512_; 
lean_del_object(v___x_474_);
v_a_499_ = lean_ctor_get(v_a_495_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_495_);
if (v_isSharedCheck_512_ == 0)
{
v___x_501_ = v_a_495_;
v_isShared_502_ = v_isSharedCheck_512_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v_a_495_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_512_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 1);
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_511_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v_snd_472_);
lean_ctor_set(v___x_479_, 0, v___x_504_);
v___x_506_ = v___x_479_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_snd_472_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_506_);
v___x_508_ = v___x_497_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
else
{
lean_object* v_a_513_; 
lean_del_object(v___x_497_);
lean_del_object(v___x_479_);
lean_dec(v_snd_472_);
v_a_513_ = lean_ctor_get(v_a_495_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v_a_495_, 1);
v_a_484_ = v_a_513_;
goto v___jp_483_;
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_del_object(v___x_479_);
lean_del_object(v___x_474_);
lean_dec(v_snd_472_);
v_a_515_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_494_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_494_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
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
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_del_object(v___x_479_);
lean_dec_ref(v_p_477_);
lean_del_object(v___x_474_);
lean_dec(v_snd_472_);
v_a_536_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_491_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_491_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
v___jp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_a_484_);
lean_ctor_set(v___x_474_, 0, v___x_482_);
v___x_486_ = v___x_474_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_a_484_);
v___x_486_ = v_reuseFailAlloc_490_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_add(v_i_457_, v___x_487_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_453_, v_isLower_454_, v_as_455_, v_sz_456_, v___x_488_, v___x_486_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_489_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_548_ = _args[0];
lean_object* v_isLower_549_ = _args[1];
lean_object* v_as_550_ = _args[2];
lean_object* v_sz_551_ = _args[3];
lean_object* v_i_552_ = _args[4];
lean_object* v_b_553_ = _args[5];
lean_object* v___y_554_ = _args[6];
lean_object* v___y_555_ = _args[7];
lean_object* v___y_556_ = _args[8];
lean_object* v___y_557_ = _args[9];
lean_object* v___y_558_ = _args[10];
lean_object* v___y_559_ = _args[11];
lean_object* v___y_560_ = _args[12];
lean_object* v___y_561_ = _args[13];
lean_object* v___y_562_ = _args[14];
lean_object* v___y_563_ = _args[15];
lean_object* v___y_564_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_565_; size_t v_sz_boxed_566_; size_t v_i_boxed_567_; lean_object* v_res_568_; 
v_isLower_boxed_565_ = lean_unbox(v_isLower_549_);
v_sz_boxed_566_ = lean_unbox_usize(v_sz_551_);
lean_dec(v_sz_551_);
v_i_boxed_567_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_res_568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_548_, v_isLower_boxed_565_, v_as_550_, v_sz_boxed_566_, v_i_boxed_567_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v_as_550_);
lean_dec(v_____s_548_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object* v_____s_569_, uint8_t v_isLower_570_, lean_object* v_as_571_, size_t v_sz_572_, size_t v_i_573_, lean_object* v_b_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
uint8_t v___x_586_; 
v___x_586_ = lean_usize_dec_lt(v_i_573_, v_sz_572_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_b_574_);
return v___x_587_;
}
else
{
lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_655_; 
v_snd_588_ = lean_ctor_get(v_b_574_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_b_574_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_b_574_, 0);
lean_dec(v_unused_656_);
v___x_590_ = v_b_574_;
v_isShared_591_ = v_isSharedCheck_655_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_dec(v_b_574_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_655_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_a_592_; lean_object* v_p_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_653_; 
v_a_592_ = lean_array_uget(v_as_571_, v_i_573_);
v_p_593_ = lean_ctor_get(v_a_592_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_a_592_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_a_592_, 1);
lean_dec(v_unused_654_);
v___x_595_ = v_a_592_;
v_isShared_596_ = v_isSharedCheck_653_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_p_593_);
lean_dec(v_a_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_653_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_a_599_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_597_ = lean_box(0);
v___x_606_ = lean_box(0);
v___x_607_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_593_, v_____s_569_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_dec_ref_known(v___x_607_, 1);
if (lean_obj_tag(v_p_593_) == 1)
{
lean_object* v_k_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_k_632_ = lean_ctor_get(v_p_593_, 0);
lean_inc(v_k_632_);
lean_dec_ref_known(v_p_593_, 3);
v___x_633_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_634_ = lean_int_dec_lt(v_k_632_, v___x_633_);
lean_dec(v_k_632_);
if (v___x_634_ == 0)
{
if (v_isLower_570_ == 0)
{
lean_del_object(v___x_595_);
lean_dec(v_snd_588_);
v_a_599_ = v___x_606_;
goto v___jp_598_;
}
else
{
goto v___jp_608_;
}
}
else
{
if (v_isLower_570_ == 0)
{
goto v___jp_608_;
}
else
{
lean_del_object(v___x_595_);
lean_dec(v_snd_588_);
v_a_599_ = v___x_606_;
goto v___jp_598_;
}
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_del_object(v___x_595_);
lean_dec_ref(v_p_593_);
lean_dec(v_snd_588_);
v___x_635_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_636_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_635_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_dec_ref_known(v___x_636_, 1);
v_a_599_ = v___x_606_;
goto v___jp_598_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_del_object(v___x_590_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
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
v___jp_608_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_610_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_609_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_623_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_623_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
if (lean_obj_tag(v_a_611_) == 0)
{
lean_object* v___x_615_; lean_object* v___x_617_; 
lean_del_object(v___x_590_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v_a_611_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v_snd_588_);
lean_ctor_set(v___x_595_, 0, v___x_615_);
v___x_617_ = v___x_595_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_snd_588_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_617_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
lean_object* v_a_622_; 
lean_del_object(v___x_613_);
lean_del_object(v___x_595_);
lean_dec(v_snd_588_);
v_a_622_ = lean_ctor_get(v_a_611_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v_a_611_, 1);
v_a_599_ = v_a_622_;
goto v___jp_598_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_dec(v_snd_588_);
v_a_624_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_610_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_610_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_del_object(v___x_595_);
lean_dec_ref(v_p_593_);
lean_del_object(v___x_590_);
lean_dec(v_snd_588_);
v_a_645_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_607_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_607_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
v___jp_598_:
{
lean_object* v___x_601_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_a_599_);
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_601_ = v___x_590_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_599_);
v___x_601_ = v_reuseFailAlloc_605_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
size_t v___x_602_; size_t v___x_603_; 
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_573_, v___x_602_);
v_i_573_ = v___x_603_;
v_b_574_ = v___x_601_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_____s_657_ = _args[0];
lean_object* v_isLower_658_ = _args[1];
lean_object* v_as_659_ = _args[2];
lean_object* v_sz_660_ = _args[3];
lean_object* v_i_661_ = _args[4];
lean_object* v_b_662_ = _args[5];
lean_object* v___y_663_ = _args[6];
lean_object* v___y_664_ = _args[7];
lean_object* v___y_665_ = _args[8];
lean_object* v___y_666_ = _args[9];
lean_object* v___y_667_ = _args[10];
lean_object* v___y_668_ = _args[11];
lean_object* v___y_669_ = _args[12];
lean_object* v___y_670_ = _args[13];
lean_object* v___y_671_ = _args[14];
lean_object* v___y_672_ = _args[15];
lean_object* v___y_673_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_674_; size_t v_sz_boxed_675_; size_t v_i_boxed_676_; lean_object* v_res_677_; 
v_isLower_boxed_674_ = lean_unbox(v_isLower_658_);
v_sz_boxed_675_ = lean_unbox_usize(v_sz_660_);
lean_dec(v_sz_660_);
v_i_boxed_676_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_657_, v_isLower_boxed_674_, v_as_659_, v_sz_boxed_675_, v_i_boxed_676_, v_b_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v_as_659_);
lean_dec(v_____s_657_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object* v_____s_678_, uint8_t v_isLower_679_, lean_object* v_as_680_, size_t v_sz_681_, size_t v_i_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v___x_695_; 
v___x_695_ = lean_usize_dec_lt(v_i_682_, v_sz_681_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v_b_683_);
return v___x_696_;
}
else
{
lean_object* v_snd_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_764_; 
v_snd_697_ = lean_ctor_get(v_b_683_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_b_683_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v_b_683_, 0);
lean_dec(v_unused_765_);
v___x_699_ = v_b_683_;
v_isShared_700_ = v_isSharedCheck_764_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snd_697_);
lean_dec(v_b_683_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_764_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_a_701_; lean_object* v_p_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_762_; 
v_a_701_ = lean_array_uget(v_as_680_, v_i_682_);
v_p_702_ = lean_ctor_get(v_a_701_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_701_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v_a_701_, 1);
lean_dec(v_unused_763_);
v___x_704_ = v_a_701_;
v_isShared_705_ = v_isSharedCheck_762_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_p_702_);
lean_dec(v_a_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_762_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_709_; lean_object* v___x_716_; 
v___x_706_ = lean_box(0);
v___x_707_ = lean_box(0);
v___x_716_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_702_, v_____s_678_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_dec_ref_known(v___x_716_, 1);
if (lean_obj_tag(v_p_702_) == 1)
{
lean_object* v_k_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_k_741_ = lean_ctor_get(v_p_702_, 0);
lean_inc(v_k_741_);
lean_dec_ref_known(v_p_702_, 3);
v___x_742_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_743_ = lean_int_dec_lt(v_k_741_, v___x_742_);
lean_dec(v_k_741_);
if (v___x_743_ == 0)
{
if (v_isLower_679_ == 0)
{
lean_del_object(v___x_704_);
lean_dec(v_snd_697_);
v_a_709_ = v___x_706_;
goto v___jp_708_;
}
else
{
goto v___jp_717_;
}
}
else
{
if (v_isLower_679_ == 0)
{
goto v___jp_717_;
}
else
{
lean_del_object(v___x_704_);
lean_dec(v_snd_697_);
v_a_709_ = v___x_706_;
goto v___jp_708_;
}
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_del_object(v___x_704_);
lean_dec_ref(v_p_702_);
lean_dec(v_snd_697_);
v___x_744_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_745_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_744_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_dec_ref_known(v___x_745_, 1);
v_a_709_ = v___x_706_;
goto v___jp_708_;
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_del_object(v___x_699_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_719_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_718_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_732_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_732_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
if (lean_obj_tag(v_a_720_) == 0)
{
lean_object* v___x_724_; lean_object* v___x_726_; 
lean_del_object(v___x_699_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_a_720_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v_snd_697_);
lean_ctor_set(v___x_704_, 0, v___x_724_);
v___x_726_ = v___x_704_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_snd_697_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; 
lean_del_object(v___x_722_);
lean_del_object(v___x_704_);
lean_dec(v_snd_697_);
v_a_731_ = lean_ctor_get(v_a_720_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v_a_720_, 1);
v_a_709_ = v_a_731_;
goto v___jp_708_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_del_object(v___x_704_);
lean_del_object(v___x_699_);
lean_dec(v_snd_697_);
v_a_733_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_719_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_719_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_del_object(v___x_704_);
lean_dec_ref(v_p_702_);
lean_del_object(v___x_699_);
lean_dec(v_snd_697_);
v_a_754_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_716_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_716_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
v___jp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v_a_709_);
lean_ctor_set(v___x_699_, 0, v___x_707_);
v___x_711_ = v___x_699_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_a_709_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; 
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_add(v_i_682_, v___x_712_);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_678_, v_isLower_679_, v_as_680_, v_sz_681_, v___x_713_, v___x_711_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_714_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_____s_766_ = _args[0];
lean_object* v_isLower_767_ = _args[1];
lean_object* v_as_768_ = _args[2];
lean_object* v_sz_769_ = _args[3];
lean_object* v_i_770_ = _args[4];
lean_object* v_b_771_ = _args[5];
lean_object* v___y_772_ = _args[6];
lean_object* v___y_773_ = _args[7];
lean_object* v___y_774_ = _args[8];
lean_object* v___y_775_ = _args[9];
lean_object* v___y_776_ = _args[10];
lean_object* v___y_777_ = _args[11];
lean_object* v___y_778_ = _args[12];
lean_object* v___y_779_ = _args[13];
lean_object* v___y_780_ = _args[14];
lean_object* v___y_781_ = _args[15];
lean_object* v___y_782_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_783_; size_t v_sz_boxed_784_; size_t v_i_boxed_785_; lean_object* v_res_786_; 
v_isLower_boxed_783_ = lean_unbox(v_isLower_767_);
v_sz_boxed_784_ = lean_unbox_usize(v_sz_769_);
lean_dec(v_sz_769_);
v_i_boxed_785_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_766_, v_isLower_boxed_783_, v_as_768_, v_sz_boxed_784_, v_i_boxed_785_, v_b_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v_as_768_);
lean_dec(v_____s_766_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(lean_object* v_init_787_, lean_object* v_____s_788_, uint8_t v_isLower_789_, lean_object* v_n_790_, lean_object* v_b_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
if (lean_obj_tag(v_n_790_) == 0)
{
lean_object* v_cs_803_; lean_object* v___x_804_; lean_object* v___x_805_; size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v_cs_803_ = lean_ctor_get(v_n_790_, 0);
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_b_791_);
v_sz_806_ = lean_array_size(v_cs_803_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_787_, v_____s_788_, v_isLower_789_, v_cs_803_, v_sz_806_, v___x_807_, v___x_805_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_823_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_823_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_823_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_823_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_fst_813_; 
v_fst_813_ = lean_ctor_get(v_a_809_, 0);
if (lean_obj_tag(v_fst_813_) == 0)
{
lean_object* v_snd_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v_snd_814_ = lean_ctor_get(v_a_809_, 1);
lean_inc(v_snd_814_);
lean_dec(v_a_809_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v_snd_814_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_object* v_val_819_; lean_object* v___x_821_; 
lean_inc_ref(v_fst_813_);
lean_dec(v_a_809_);
v_val_819_ = lean_ctor_get(v_fst_813_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v_fst_813_, 1);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_val_819_);
v___x_821_ = v___x_811_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_val_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_808_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_808_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_vs_832_; lean_object* v___x_833_; lean_object* v___x_834_; size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; 
v_vs_832_ = lean_ctor_get(v_n_790_, 0);
v___x_833_ = lean_box(0);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v_b_791_);
v_sz_835_ = lean_array_size(v_vs_832_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_788_, v_isLower_789_, v_vs_832_, v_sz_835_, v___x_836_, v___x_834_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_852_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_852_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_852_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_852_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_fst_842_; 
v_fst_842_ = lean_ctor_get(v_a_838_, 0);
if (lean_obj_tag(v_fst_842_) == 0)
{
lean_object* v_snd_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v_snd_843_ = lean_ctor_get(v_a_838_, 1);
lean_inc(v_snd_843_);
lean_dec(v_a_838_);
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_snd_843_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_844_);
v___x_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v_val_848_; lean_object* v___x_850_; 
lean_inc_ref(v_fst_842_);
lean_dec(v_a_838_);
v_val_848_ = lean_ctor_get(v_fst_842_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v_fst_842_, 1);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_val_848_);
v___x_850_ = v___x_840_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_val_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_837_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_837_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_init_861_, lean_object* v_____s_862_, uint8_t v_isLower_863_, lean_object* v_as_864_, size_t v_sz_865_, size_t v_i_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_lt(v_i_866_, v_sz_865_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_b_867_);
return v___x_880_;
}
else
{
lean_object* v_snd_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_915_; 
v_snd_881_ = lean_ctor_get(v_b_867_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_b_867_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_b_867_, 0);
lean_dec(v_unused_916_);
v___x_883_ = v_b_867_;
v_isShared_884_ = v_isSharedCheck_915_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_snd_881_);
lean_dec(v_b_867_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_915_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_887_; 
v___x_885_ = lean_box(0);
v_a_886_ = lean_array_uget_borrowed(v_as_864_, v_i_866_);
lean_inc(v_snd_881_);
v___x_887_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_861_, v_____s_862_, v_isLower_863_, v_a_886_, v_snd_881_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_906_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_906_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_906_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_906_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
if (lean_obj_tag(v_a_888_) == 0)
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v_a_888_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_892_);
v___x_894_ = v___x_883_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_snd_881_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_894_);
v___x_896_ = v___x_890_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; 
lean_del_object(v___x_890_);
lean_dec(v_snd_881_);
v_a_899_ = lean_ctor_get(v_a_888_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v_a_888_, 1);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_a_899_);
lean_ctor_set(v___x_883_, 0, v___x_885_);
v___x_901_ = v___x_883_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_a_899_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
size_t v___x_902_; size_t v___x_903_; 
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_add(v_i_866_, v___x_902_);
v_i_866_ = v___x_903_;
v_b_867_ = v___x_901_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_del_object(v___x_883_);
lean_dec(v_snd_881_);
v_a_907_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_887_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_887_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_917_ = _args[0];
lean_object* v_____s_918_ = _args[1];
lean_object* v_isLower_919_ = _args[2];
lean_object* v_as_920_ = _args[3];
lean_object* v_sz_921_ = _args[4];
lean_object* v_i_922_ = _args[5];
lean_object* v_b_923_ = _args[6];
lean_object* v___y_924_ = _args[7];
lean_object* v___y_925_ = _args[8];
lean_object* v___y_926_ = _args[9];
lean_object* v___y_927_ = _args[10];
lean_object* v___y_928_ = _args[11];
lean_object* v___y_929_ = _args[12];
lean_object* v___y_930_ = _args[13];
lean_object* v___y_931_ = _args[14];
lean_object* v___y_932_ = _args[15];
lean_object* v___y_933_ = _args[16];
lean_object* v___y_934_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_935_; size_t v_sz_boxed_936_; size_t v_i_boxed_937_; lean_object* v_res_938_; 
v_isLower_boxed_935_ = lean_unbox(v_isLower_919_);
v_sz_boxed_936_ = lean_unbox_usize(v_sz_921_);
lean_dec(v_sz_921_);
v_i_boxed_937_ = lean_unbox_usize(v_i_922_);
lean_dec(v_i_922_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_917_, v_____s_918_, v_isLower_boxed_935_, v_as_920_, v_sz_boxed_936_, v_i_boxed_937_, v_b_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v_as_920_);
lean_dec(v_____s_918_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1___boxed(lean_object* v_init_939_, lean_object* v_____s_940_, lean_object* v_isLower_941_, lean_object* v_n_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
uint8_t v_isLower_boxed_955_; lean_object* v_res_956_; 
v_isLower_boxed_955_ = lean_unbox(v_isLower_941_);
v_res_956_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_939_, v_____s_940_, v_isLower_boxed_955_, v_n_942_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v_n_942_);
lean_dec(v_____s_940_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(lean_object* v_____s_957_, uint8_t v_isLower_958_, lean_object* v_t_959_, lean_object* v_init_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_root_972_; lean_object* v_tail_973_; lean_object* v___x_974_; 
v_root_972_ = lean_ctor_get(v_t_959_, 0);
v_tail_973_ = lean_ctor_get(v_t_959_, 1);
v___x_974_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_960_, v_____s_957_, v_isLower_958_, v_root_972_, v_init_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1011_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_1011_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1011_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
if (lean_obj_tag(v_a_975_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v_a_975_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v_a_975_, 1);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_a_979_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; size_t v_sz_986_; size_t v___x_987_; lean_object* v___x_988_; 
lean_del_object(v___x_977_);
v_a_983_ = lean_ctor_get(v_a_975_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v_a_975_, 1);
v___x_984_ = lean_box(0);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v_a_983_);
v_sz_986_ = lean_array_size(v_tail_973_);
v___x_987_ = ((size_t)0ULL);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_957_, v_isLower_958_, v_tail_973_, v_sz_986_, v___x_987_, v___x_985_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1002_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_fst_993_; 
v_fst_993_ = lean_ctor_get(v_a_989_, 0);
if (lean_obj_tag(v_fst_993_) == 0)
{
lean_object* v_snd_994_; lean_object* v___x_996_; 
v_snd_994_ = lean_ctor_get(v_a_989_, 1);
lean_inc(v_snd_994_);
lean_dec(v_a_989_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_snd_994_);
v___x_996_ = v___x_991_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_snd_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v_val_998_; lean_object* v___x_1000_; 
lean_inc_ref(v_fst_993_);
lean_dec(v_a_989_);
v_val_998_ = lean_ctor_get(v_fst_993_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_fst_993_, 1);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_val_998_);
v___x_1000_ = v___x_991_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_val_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_988_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_988_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_974_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_974_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1020_, lean_object* v_isLower_1021_, lean_object* v_t_1022_, lean_object* v_init_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v_isLower_boxed_1035_; lean_object* v_res_1036_; 
v_isLower_boxed_1035_ = lean_unbox(v_isLower_1021_);
v_res_1036_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_____s_1020_, v_isLower_boxed_1035_, v_t_1022_, v_init_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v_t_1022_);
lean_dec(v_____s_1020_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1037_, lean_object* v_as_1038_, size_t v_sz_1039_, size_t v_i_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_usize_dec_lt(v_i_1040_, v_sz_1039_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_b_1041_);
return v___x_1054_;
}
else
{
lean_object* v_snd_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1079_; 
v_snd_1055_ = lean_ctor_get(v_b_1041_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_b_1041_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v_b_1041_, 0);
lean_dec(v_unused_1080_);
v___x_1057_ = v_b_1041_;
v_isShared_1058_ = v_isSharedCheck_1079_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_snd_1055_);
lean_dec(v_b_1041_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1079_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1059_ = lean_box(0);
v_a_1060_ = lean_array_uget_borrowed(v_as_1038_, v_i_1040_);
v___x_1061_ = lean_box(0);
v___x_1062_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1055_, v_isLower_1037_, v_a_1060_, v___x_1061_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
lean_dec_ref_known(v___x_1062_, 1);
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_snd_1055_, v___x_1063_);
lean_dec(v_snd_1055_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v___x_1064_);
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1066_ = v___x_1057_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
size_t v___x_1067_; size_t v___x_1068_; 
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_add(v_i_1040_, v___x_1067_);
v_i_1040_ = v___x_1068_;
v_b_1041_ = v___x_1066_;
goto _start;
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_1057_);
lean_dec(v_snd_1055_);
v_a_1071_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1062_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1062_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object* v_isLower_1081_, lean_object* v_as_1082_, lean_object* v_sz_1083_, lean_object* v_i_1084_, lean_object* v_b_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
uint8_t v_isLower_boxed_1097_; size_t v_sz_boxed_1098_; size_t v_i_boxed_1099_; lean_object* v_res_1100_; 
v_isLower_boxed_1097_ = lean_unbox(v_isLower_1081_);
v_sz_boxed_1098_ = lean_unbox_usize(v_sz_1083_);
lean_dec(v_sz_1083_);
v_i_boxed_1099_ = lean_unbox_usize(v_i_1084_);
lean_dec(v_i_1084_);
v_res_1100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_1097_, v_as_1082_, v_sz_boxed_1098_, v_i_boxed_1099_, v_b_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v_as_1082_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1101_, lean_object* v_as_1102_, size_t v_sz_1103_, size_t v_i_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_usize_dec_lt(v_i_1104_, v_sz_1103_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_b_1105_);
return v___x_1118_;
}
else
{
lean_object* v_snd_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1143_; 
v_snd_1119_ = lean_ctor_get(v_b_1105_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_b_1105_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v_b_1105_, 0);
lean_dec(v_unused_1144_);
v___x_1121_ = v_b_1105_;
v_isShared_1122_ = v_isSharedCheck_1143_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_snd_1119_);
lean_dec(v_b_1105_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1143_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v_a_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = lean_box(0);
v_a_1124_ = lean_array_uget_borrowed(v_as_1102_, v_i_1104_);
v___x_1125_ = lean_box(0);
v___x_1126_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1119_, v_isLower_1101_, v_a_1124_, v___x_1125_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_dec_ref_known(v___x_1126_, 1);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_snd_1119_, v___x_1127_);
lean_dec(v_snd_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1128_);
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1130_ = v___x_1121_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = ((size_t)1ULL);
v___x_1132_ = lean_usize_add(v_i_1104_, v___x_1131_);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1101_, v_as_1102_, v_sz_1103_, v___x_1132_, v___x_1130_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1133_;
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_del_object(v___x_1121_);
lean_dec(v_snd_1119_);
v_a_1135_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1126_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1126_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5___boxed(lean_object* v_isLower_1145_, lean_object* v_as_1146_, lean_object* v_sz_1147_, lean_object* v_i_1148_, lean_object* v_b_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
uint8_t v_isLower_boxed_1161_; size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_isLower_boxed_1161_ = lean_unbox(v_isLower_1145_);
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1147_);
lean_dec(v_sz_1147_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1148_);
lean_dec(v_i_1148_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1161_, v_as_1146_, v_sz_boxed_1162_, v_i_boxed_1163_, v_b_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v_as_1146_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1165_, lean_object* v_as_1166_, size_t v_sz_1167_, size_t v_i_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_lt(v_i_1168_, v_sz_1167_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_b_1169_);
return v___x_1182_;
}
else
{
lean_object* v_snd_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1207_; 
v_snd_1183_ = lean_ctor_get(v_b_1169_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_b_1169_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_b_1169_, 0);
lean_dec(v_unused_1208_);
v___x_1185_ = v_b_1169_;
v_isShared_1186_ = v_isSharedCheck_1207_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1183_);
lean_dec(v_b_1169_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1207_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1187_ = lean_box(0);
v_a_1188_ = lean_array_uget_borrowed(v_as_1166_, v_i_1168_);
v___x_1189_ = lean_box(0);
v___x_1190_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1183_, v_isLower_1165_, v_a_1188_, v___x_1189_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_dec_ref_known(v___x_1190_, 1);
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_snd_1183_, v___x_1191_);
lean_dec(v_snd_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1192_);
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1194_ = v___x_1185_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
size_t v___x_1195_; size_t v___x_1196_; 
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_add(v_i_1168_, v___x_1195_);
v_i_1168_ = v___x_1196_;
v_b_1169_ = v___x_1194_;
goto _start;
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_del_object(v___x_1185_);
lean_dec(v_snd_1183_);
v_a_1199_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1190_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1190_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object* v_isLower_1209_, lean_object* v_as_1210_, lean_object* v_sz_1211_, lean_object* v_i_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v_isLower_boxed_1225_; size_t v_sz_boxed_1226_; size_t v_i_boxed_1227_; lean_object* v_res_1228_; 
v_isLower_boxed_1225_ = lean_unbox(v_isLower_1209_);
v_sz_boxed_1226_ = lean_unbox_usize(v_sz_1211_);
lean_dec(v_sz_1211_);
v_i_boxed_1227_ = lean_unbox_usize(v_i_1212_);
lean_dec(v_i_1212_);
v_res_1228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1225_, v_as_1210_, v_sz_boxed_1226_, v_i_boxed_1227_, v_b_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v_as_1210_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1229_, lean_object* v_as_1230_, size_t v_sz_1231_, size_t v_i_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_usize_dec_lt(v_i_1232_, v_sz_1231_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_b_1233_);
return v___x_1246_;
}
else
{
lean_object* v_snd_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1271_; 
v_snd_1247_ = lean_ctor_get(v_b_1233_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_b_1233_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_b_1233_, 0);
lean_dec(v_unused_1272_);
v___x_1249_ = v_b_1233_;
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snd_1247_);
lean_dec(v_b_1233_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = lean_box(0);
v_a_1252_ = lean_array_uget_borrowed(v_as_1230_, v_i_1232_);
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1247_, v_isLower_1229_, v_a_1252_, v___x_1253_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_dec_ref_known(v___x_1254_, 1);
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = lean_nat_add(v_snd_1247_, v___x_1255_);
lean_dec(v_snd_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1256_);
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1258_ = v___x_1249_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_add(v_i_1232_, v___x_1259_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1229_, v_as_1230_, v_sz_1231_, v___x_1260_, v___x_1258_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1261_;
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_del_object(v___x_1249_);
lean_dec(v_snd_1247_);
v_a_1263_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1254_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1254_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object* v_isLower_1273_, lean_object* v_as_1274_, lean_object* v_sz_1275_, lean_object* v_i_1276_, lean_object* v_b_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v_isLower_boxed_1289_; size_t v_sz_boxed_1290_; size_t v_i_boxed_1291_; lean_object* v_res_1292_; 
v_isLower_boxed_1289_ = lean_unbox(v_isLower_1273_);
v_sz_boxed_1290_ = lean_unbox_usize(v_sz_1275_);
lean_dec(v_sz_1275_);
v_i_boxed_1291_ = lean_unbox_usize(v_i_1276_);
lean_dec(v_i_1276_);
v_res_1292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1289_, v_as_1274_, v_sz_boxed_1290_, v_i_boxed_1291_, v_b_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v_as_1274_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(lean_object* v_init_1293_, uint8_t v_isLower_1294_, lean_object* v_n_1295_, lean_object* v_b_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
if (lean_obj_tag(v_n_1295_) == 0)
{
lean_object* v_cs_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v_cs_1308_ = lean_ctor_get(v_n_1295_, 0);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v_b_1296_);
v_sz_1311_ = lean_array_size(v_cs_1308_);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1293_, v_isLower_1294_, v_cs_1308_, v_sz_1311_, v___x_1312_, v___x_1310_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1328_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_fst_1318_; 
v_fst_1318_ = lean_ctor_get(v_a_1314_, 0);
if (lean_obj_tag(v_fst_1318_) == 0)
{
lean_object* v_snd_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v_snd_1319_ = lean_ctor_get(v_a_1314_, 1);
lean_inc(v_snd_1319_);
lean_dec(v_a_1314_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_snd_1319_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1320_);
v___x_1322_ = v___x_1316_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1326_; 
lean_inc_ref(v_fst_1318_);
lean_dec(v_a_1314_);
v_val_1324_ = lean_ctor_get(v_fst_1318_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v_fst_1318_, 1);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_val_1324_);
v___x_1326_ = v___x_1316_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_val_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1313_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1313_);
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
else
{
lean_object* v_vs_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; size_t v_sz_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v_vs_1337_ = lean_ctor_get(v_n_1295_, 0);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v_b_1296_);
v_sz_1340_ = lean_array_size(v_vs_1337_);
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1294_, v_vs_1337_, v_sz_1340_, v___x_1341_, v___x_1339_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1357_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1357_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1357_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_fst_1347_; 
v_fst_1347_ = lean_ctor_get(v_a_1343_, 0);
if (lean_obj_tag(v_fst_1347_) == 0)
{
lean_object* v_snd_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v_snd_1348_ = lean_ctor_get(v_a_1343_, 1);
lean_inc(v_snd_1348_);
lean_dec(v_a_1343_);
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_snd_1348_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1355_; 
lean_inc_ref(v_fst_1347_);
lean_dec(v_a_1343_);
v_val_1353_ = lean_ctor_get(v_fst_1347_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_fst_1347_, 1);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_val_1353_);
v___x_1355_ = v___x_1345_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_val_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
v_a_1358_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1342_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1342_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object* v_init_1366_, uint8_t v_isLower_1367_, lean_object* v_as_1368_, size_t v_sz_1369_, size_t v_i_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_usize_dec_lt(v_i_1370_, v_sz_1369_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_b_1371_);
return v___x_1384_;
}
else
{
lean_object* v_snd_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1419_; 
v_snd_1385_ = lean_ctor_get(v_b_1371_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_b_1371_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v_b_1371_, 0);
lean_dec(v_unused_1420_);
v___x_1387_ = v_b_1371_;
v_isShared_1388_ = v_isSharedCheck_1419_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_snd_1385_);
lean_dec(v_b_1371_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1419_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v_a_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_box(0);
v_a_1390_ = lean_array_uget_borrowed(v_as_1368_, v_i_1370_);
lean_inc(v_snd_1385_);
v___x_1391_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1366_, v_isLower_1367_, v_a_1390_, v_snd_1385_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1410_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1410_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1410_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
if (lean_obj_tag(v_a_1392_) == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_a_1392_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1396_);
v___x_1398_ = v___x_1387_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_snd_1385_);
v___x_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1398_);
v___x_1400_ = v___x_1394_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; 
lean_del_object(v___x_1394_);
lean_dec(v_snd_1385_);
v_a_1403_ = lean_ctor_get(v_a_1392_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v_a_1392_, 1);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v_a_1403_);
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1405_ = v___x_1387_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_a_1403_);
v___x_1405_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
size_t v___x_1406_; size_t v___x_1407_; 
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_add(v_i_1370_, v___x_1406_);
v_i_1370_ = v___x_1407_;
v_b_1371_ = v___x_1405_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
v_a_1411_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1391_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1391_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_init_1421_ = _args[0];
lean_object* v_isLower_1422_ = _args[1];
lean_object* v_as_1423_ = _args[2];
lean_object* v_sz_1424_ = _args[3];
lean_object* v_i_1425_ = _args[4];
lean_object* v_b_1426_ = _args[5];
lean_object* v___y_1427_ = _args[6];
lean_object* v___y_1428_ = _args[7];
lean_object* v___y_1429_ = _args[8];
lean_object* v___y_1430_ = _args[9];
lean_object* v___y_1431_ = _args[10];
lean_object* v___y_1432_ = _args[11];
lean_object* v___y_1433_ = _args[12];
lean_object* v___y_1434_ = _args[13];
lean_object* v___y_1435_ = _args[14];
lean_object* v___y_1436_ = _args[15];
lean_object* v___y_1437_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1438_; size_t v_sz_boxed_1439_; size_t v_i_boxed_1440_; lean_object* v_res_1441_; 
v_isLower_boxed_1438_ = lean_unbox(v_isLower_1422_);
v_sz_boxed_1439_ = lean_unbox_usize(v_sz_1424_);
lean_dec(v_sz_1424_);
v_i_boxed_1440_ = lean_unbox_usize(v_i_1425_);
lean_dec(v_i_1425_);
v_res_1441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1421_, v_isLower_boxed_1438_, v_as_1423_, v_sz_boxed_1439_, v_i_boxed_1440_, v_b_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v_as_1423_);
lean_dec(v_init_1421_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_init_1442_, lean_object* v_isLower_1443_, lean_object* v_n_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v_isLower_boxed_1457_; lean_object* v_res_1458_; 
v_isLower_boxed_1457_ = lean_unbox(v_isLower_1443_);
v_res_1458_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1442_, v_isLower_boxed_1457_, v_n_1444_, v_b_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v_n_1444_);
lean_dec(v_init_1442_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(uint8_t v_isLower_1459_, lean_object* v_t_1460_, lean_object* v_init_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_root_1473_; lean_object* v_tail_1474_; lean_object* v___x_1475_; 
v_root_1473_ = lean_ctor_get(v_t_1460_, 0);
v_tail_1474_ = lean_ctor_get(v_t_1460_, 1);
lean_inc(v_init_1461_);
v___x_1475_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1461_, v_isLower_1459_, v_root_1473_, v_init_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v_init_1461_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1512_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1512_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1512_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
if (lean_obj_tag(v_a_1476_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; 
v_a_1480_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v_a_1476_, 1);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v_a_1480_);
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; size_t v_sz_1487_; size_t v___x_1488_; lean_object* v___x_1489_; 
lean_del_object(v___x_1478_);
v_a_1484_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v_a_1476_, 1);
v___x_1485_ = lean_box(0);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v_a_1484_);
v_sz_1487_ = lean_array_size(v_tail_1474_);
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_1459_, v_tail_1474_, v_sz_1487_, v___x_1488_, v___x_1486_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1503_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_fst_1494_; 
v_fst_1494_ = lean_ctor_get(v_a_1490_, 0);
if (lean_obj_tag(v_fst_1494_) == 0)
{
lean_object* v_snd_1495_; lean_object* v___x_1497_; 
v_snd_1495_ = lean_ctor_get(v_a_1490_, 1);
lean_inc(v_snd_1495_);
lean_dec(v_a_1490_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_snd_1495_);
v___x_1497_ = v___x_1492_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_snd_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
else
{
lean_object* v_val_1499_; lean_object* v___x_1501_; 
lean_inc_ref(v_fst_1494_);
lean_dec(v_a_1490_);
v_val_1499_ = lean_ctor_get(v_fst_1494_, 0);
lean_inc(v_val_1499_);
lean_dec_ref_known(v_fst_1494_, 1);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_val_1499_);
v___x_1501_ = v___x_1492_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_val_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_a_1504_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1489_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1489_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_a_1513_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1475_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1475_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1521_, lean_object* v_t_1522_, lean_object* v_init_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v_isLower_boxed_1535_; lean_object* v_res_1536_; 
v_isLower_boxed_1535_ = lean_unbox(v_isLower_1521_);
v_res_1536_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_boxed_1535_, v_t_1522_, v_init_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v_t_1522_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(lean_object* v_css_1537_, uint8_t v_isLower_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_x_1550_; lean_object* v___x_1551_; 
v_x_1550_ = lean_unsigned_to_nat(0u);
v___x_1551_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_1538_, v_css_1537_, v_x_1550_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1559_; 
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v___x_1551_, 0);
lean_dec(v_unused_1560_);
v___x_1553_ = v___x_1551_;
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v___x_1551_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = lean_box(0);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1555_);
v___x_1557_ = v___x_1553_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1551_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1551_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs___boxed(lean_object* v_css_1569_, lean_object* v_isLower_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
uint8_t v_isLower_boxed_1582_; lean_object* v_res_1583_; 
v_isLower_boxed_1582_ = lean_unbox(v_isLower_1570_);
v_res_1583_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_css_1569_, v_isLower_boxed_1582_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_css_1569_);
return v_res_1583_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1586_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1));
v___x_1587_ = lean_unsigned_to_nat(2u);
v___x_1588_ = lean_unsigned_to_nat(55u);
v___x_1589_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0));
v___x_1590_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1591_ = l_mkPanicMessageWithDecl(v___x_1590_, v___x_1589_, v___x_1588_, v___x_1587_, v___x_1586_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1592_, v_a_1600_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v_lowers_1605_; lean_object* v_vars_1606_; lean_object* v_size_1607_; lean_object* v_size_1608_; uint8_t v___x_1609_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v_lowers_1605_ = lean_ctor_get(v_a_1604_, 6);
lean_inc_ref(v_lowers_1605_);
v_vars_1606_ = lean_ctor_get(v_a_1604_, 0);
lean_inc_ref(v_vars_1606_);
lean_dec(v_a_1604_);
v_size_1607_ = lean_ctor_get(v_lowers_1605_, 2);
v_size_1608_ = lean_ctor_get(v_vars_1606_, 2);
lean_inc(v_size_1608_);
lean_dec_ref(v_vars_1606_);
v___x_1609_ = lean_nat_dec_eq(v_size_1607_, v_size_1608_);
lean_dec(v_size_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v_lowers_1605_);
v___x_1610_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2);
v___x_1611_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_1610_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_lowers_1605_, v___x_1609_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec_ref(v_lowers_1605_);
return v___x_1612_;
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_a_1613_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1603_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1603_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___boxed(lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec(v_a_1621_);
return v_res_1632_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1635_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1));
v___x_1636_ = lean_unsigned_to_nat(2u);
v___x_1637_ = lean_unsigned_to_nat(60u);
v___x_1638_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0));
v___x_1639_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1640_ = l_mkPanicMessageWithDecl(v___x_1639_, v___x_1638_, v___x_1637_, v___x_1636_, v___x_1635_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1641_, v_a_1649_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v_uppers_1654_; lean_object* v_vars_1655_; lean_object* v_size_1656_; lean_object* v_size_1657_; uint8_t v___x_1658_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v_uppers_1654_ = lean_ctor_get(v_a_1653_, 7);
lean_inc_ref(v_uppers_1654_);
v_vars_1655_ = lean_ctor_get(v_a_1653_, 0);
lean_inc_ref(v_vars_1655_);
lean_dec(v_a_1653_);
v_size_1656_ = lean_ctor_get(v_uppers_1654_, 2);
v_size_1657_ = lean_ctor_get(v_vars_1655_, 2);
lean_inc(v_size_1657_);
lean_dec_ref(v_vars_1655_);
v___x_1658_ = lean_nat_dec_eq(v_size_1656_, v_size_1657_);
lean_dec(v_size_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec_ref(v_uppers_1654_);
v___x_1659_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2);
v___x_1660_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_1659_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1660_;
}
else
{
uint8_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = 0;
v___x_1662_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_uppers_1654_, v___x_1661_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec_ref(v_uppers_1654_);
return v___x_1662_;
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1652_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1652_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___boxed(lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec(v_a_1671_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(lean_object* v_msg_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_4077__overap_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_obj_once(&l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_4077__overap_1696_ = lean_panic_fn_borrowed(v___x_1695_, v_msg_1683_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc(v___y_1684_);
v___x_1697_ = lean_apply_11(v___x_4077__overap_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, lean_box(0));
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___boxed(lean_object* v_msg_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v_msg_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec(v___y_1699_);
return v_res_1710_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_unsigned_to_nat(1u);
v___x_1712_ = lean_nat_to_int(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2));
v___x_1716_ = lean_unsigned_to_nat(6u);
v___x_1717_ = lean_unsigned_to_nat(70u);
v___x_1718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_1719_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1720_ = l_mkPanicMessageWithDecl(v___x_1719_, v___x_1718_, v___x_1717_, v___x_1716_, v___x_1715_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1721_, size_t v_sz_1722_, size_t v_i_1723_, lean_object* v_b_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_lt(v_i_1723_, v_sz_1722_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_b_1724_);
return v___x_1737_;
}
else
{
lean_object* v_snd_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1796_; 
v_snd_1738_ = lean_ctor_get(v_b_1724_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_b_1724_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_b_1724_, 0);
lean_dec(v_unused_1797_);
v___x_1740_ = v_b_1724_;
v_isShared_1741_ = v_isSharedCheck_1796_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_snd_1738_);
lean_dec(v_b_1724_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1796_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v_a_1744_; lean_object* v_a_1754_; 
v___x_1742_ = lean_box(0);
v_a_1754_ = lean_array_uget(v_as_1721_, v_i_1723_);
if (lean_obj_tag(v_a_1754_) == 1)
{
lean_object* v_val_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1795_; 
v_val_1755_ = lean_ctor_get(v_a_1754_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1757_ = v_a_1754_;
v_isShared_1758_ = v_isSharedCheck_1795_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_val_1755_);
lean_dec(v_a_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1795_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_d_1759_; lean_object* v_p_1760_; lean_object* v___x_1761_; 
v_d_1759_ = lean_ctor_get(v_val_1755_, 0);
lean_inc(v_d_1759_);
v_p_1760_ = lean_ctor_get(v_val_1755_, 1);
lean_inc_ref(v_p_1760_);
lean_dec(v_val_1755_);
v___x_1761_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_1760_, v_snd_1738_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec_ref(v_p_1760_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
lean_dec_ref_known(v___x_1761_, 1);
v___x_1762_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1763_ = lean_int_dec_lt(v___x_1762_, v_d_1759_);
lean_dec(v_d_1759_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1765_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1764_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1778_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1778_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1778_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 0)
{
lean_object* v___x_1771_; 
lean_del_object(v___x_1740_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v_a_1766_);
v___x_1771_ = v___x_1757_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v_snd_1738_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1772_);
v___x_1774_ = v___x_1768_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
else
{
lean_object* v_a_1777_; 
lean_del_object(v___x_1768_);
lean_del_object(v___x_1757_);
lean_dec(v_snd_1738_);
v_a_1777_ = lean_ctor_get(v_a_1766_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v_a_1766_, 1);
v_a_1744_ = v_a_1777_;
goto v___jp_1743_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_del_object(v___x_1757_);
lean_del_object(v___x_1740_);
lean_dec(v_snd_1738_);
v_a_1779_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1765_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1765_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_del_object(v___x_1757_);
goto v___jp_1751_;
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_d_1759_);
lean_del_object(v___x_1757_);
lean_del_object(v___x_1740_);
lean_dec(v_snd_1738_);
v_a_1787_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1761_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1761_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
else
{
lean_dec(v_a_1754_);
goto v___jp_1751_;
}
v___jp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v_a_1744_);
lean_ctor_set(v___x_1740_, 0, v___x_1742_);
v___x_1746_ = v___x_1740_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_a_1744_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
size_t v___x_1747_; size_t v___x_1748_; 
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1723_, v___x_1747_);
v_i_1723_ = v___x_1748_;
v_b_1724_ = v___x_1746_;
goto _start;
}
}
v___jp_1751_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v_snd_1738_, v___x_1752_);
lean_dec(v_snd_1738_);
v_a_1744_ = v___x_1753_;
goto v___jp_1743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1798_, lean_object* v_sz_1799_, lean_object* v_i_1800_, lean_object* v_b_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
size_t v_sz_boxed_1813_; size_t v_i_boxed_1814_; lean_object* v_res_1815_; 
v_sz_boxed_1813_ = lean_unbox_usize(v_sz_1799_);
lean_dec(v_sz_1799_);
v_i_boxed_1814_ = lean_unbox_usize(v_i_1800_);
lean_dec(v_i_1800_);
v_res_1815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1798_, v_sz_boxed_1813_, v_i_boxed_1814_, v_b_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v_as_1798_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(lean_object* v_as_1816_, size_t v_sz_1817_, size_t v_i_1818_, lean_object* v_b_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_usize_dec_lt(v_i_1818_, v_sz_1817_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_b_1819_);
return v___x_1832_;
}
else
{
lean_object* v_snd_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1891_; 
v_snd_1833_ = lean_ctor_get(v_b_1819_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_b_1819_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; 
v_unused_1892_ = lean_ctor_get(v_b_1819_, 0);
lean_dec(v_unused_1892_);
v___x_1835_ = v_b_1819_;
v_isShared_1836_ = v_isSharedCheck_1891_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_snd_1833_);
lean_dec(v_b_1819_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1891_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v_a_1839_; lean_object* v_a_1849_; 
v___x_1837_ = lean_box(0);
v_a_1849_ = lean_array_uget(v_as_1816_, v_i_1818_);
if (lean_obj_tag(v_a_1849_) == 1)
{
lean_object* v_val_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1890_; 
v_val_1850_ = lean_ctor_get(v_a_1849_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_a_1849_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1852_ = v_a_1849_;
v_isShared_1853_ = v_isSharedCheck_1890_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_val_1850_);
lean_dec(v_a_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1890_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_d_1854_; lean_object* v_p_1855_; lean_object* v___x_1856_; 
v_d_1854_ = lean_ctor_get(v_val_1850_, 0);
lean_inc(v_d_1854_);
v_p_1855_ = lean_ctor_get(v_val_1850_, 1);
lean_inc_ref(v_p_1855_);
lean_dec(v_val_1850_);
v___x_1856_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_1855_, v_snd_1833_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec_ref(v_p_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
lean_dec_ref_known(v___x_1856_, 1);
v___x_1857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1858_ = lean_int_dec_lt(v___x_1857_, v_d_1854_);
lean_dec(v_d_1854_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1860_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1859_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1873_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1873_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1873_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
if (lean_obj_tag(v_a_1861_) == 0)
{
lean_object* v___x_1866_; 
lean_del_object(v___x_1835_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_a_1861_);
v___x_1866_ = v___x_1852_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v_snd_1833_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1867_);
v___x_1869_ = v___x_1863_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_object* v_a_1872_; 
lean_del_object(v___x_1863_);
lean_del_object(v___x_1852_);
lean_dec(v_snd_1833_);
v_a_1872_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v_a_1861_, 1);
v_a_1839_ = v_a_1872_;
goto v___jp_1838_;
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1852_);
lean_del_object(v___x_1835_);
lean_dec(v_snd_1833_);
v_a_1874_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1860_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1860_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_del_object(v___x_1852_);
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_d_1854_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1835_);
lean_dec(v_snd_1833_);
v_a_1882_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1856_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1856_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
else
{
lean_dec(v_a_1849_);
goto v___jp_1846_;
}
v___jp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 1, v_a_1839_);
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1841_ = v___x_1835_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_a_1839_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
size_t v___x_1842_; size_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = ((size_t)1ULL);
v___x_1843_ = lean_usize_add(v_i_1818_, v___x_1842_);
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1816_, v_sz_1817_, v___x_1843_, v___x_1841_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
return v___x_1844_;
}
}
v___jp_1846_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = lean_nat_add(v_snd_1833_, v___x_1847_);
lean_dec(v_snd_1833_);
v_a_1839_ = v___x_1848_;
goto v___jp_1838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1893_, lean_object* v_sz_1894_, lean_object* v_i_1895_, lean_object* v_b_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1894_);
lean_dec(v_sz_1894_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1895_);
lean_dec(v_i_1895_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_as_1893_, v_sz_boxed_1908_, v_i_boxed_1909_, v_b_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v_as_1893_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(lean_object* v_init_1911_, lean_object* v_n_1912_, lean_object* v_b_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
if (lean_obj_tag(v_n_1912_) == 0)
{
lean_object* v_cs_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; size_t v_sz_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v_cs_1925_ = lean_ctor_get(v_n_1912_, 0);
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v_b_1913_);
v_sz_1928_ = lean_array_size(v_cs_1925_);
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_1911_, v_cs_1925_, v_sz_1928_, v___x_1929_, v___x_1927_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1945_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1945_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1945_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_fst_1935_; 
v_fst_1935_ = lean_ctor_get(v_a_1931_, 0);
if (lean_obj_tag(v_fst_1935_) == 0)
{
lean_object* v_snd_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
v_snd_1936_ = lean_ctor_get(v_a_1931_, 1);
lean_inc(v_snd_1936_);
lean_dec(v_a_1931_);
v___x_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_snd_1936_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1937_);
v___x_1939_ = v___x_1933_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
else
{
lean_object* v_val_1941_; lean_object* v___x_1943_; 
lean_inc_ref(v_fst_1935_);
lean_dec(v_a_1931_);
v_val_1941_ = lean_ctor_get(v_fst_1935_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_fst_1935_, 1);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v_val_1941_);
v___x_1943_ = v___x_1933_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_val_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1930_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1930_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
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
lean_object* v_vs_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; size_t v_sz_1957_; size_t v___x_1958_; lean_object* v___x_1959_; 
v_vs_1954_ = lean_ctor_get(v_n_1912_, 0);
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v_b_1913_);
v_sz_1957_ = lean_array_size(v_vs_1954_);
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_vs_1954_, v_sz_1957_, v___x_1958_, v___x_1956_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1974_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1974_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1974_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_fst_1964_; 
v_fst_1964_ = lean_ctor_get(v_a_1960_, 0);
if (lean_obj_tag(v_fst_1964_) == 0)
{
lean_object* v_snd_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v_snd_1965_ = lean_ctor_get(v_a_1960_, 1);
lean_inc(v_snd_1965_);
lean_dec(v_a_1960_);
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_snd_1965_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1966_);
v___x_1968_ = v___x_1962_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1972_; 
lean_inc_ref(v_fst_1964_);
lean_dec(v_a_1960_);
v_val_1970_ = lean_ctor_get(v_fst_1964_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v_fst_1964_, 1);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v_val_1970_);
v___x_1972_ = v___x_1962_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_val_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1959_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1959_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(lean_object* v_init_1983_, lean_object* v_as_1984_, size_t v_sz_1985_, size_t v_i_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_lt(v_i_1986_, v_sz_1985_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_b_1987_);
return v___x_2000_;
}
else
{
lean_object* v_snd_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2035_; 
v_snd_2001_ = lean_ctor_get(v_b_1987_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_b_1987_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v_b_1987_, 0);
lean_dec(v_unused_2036_);
v___x_2003_ = v_b_1987_;
v_isShared_2004_ = v_isSharedCheck_2035_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snd_2001_);
lean_dec(v_b_1987_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2035_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v_a_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_box(0);
v_a_2006_ = lean_array_uget_borrowed(v_as_1984_, v_i_1986_);
lean_inc(v_snd_2001_);
v___x_2007_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_1983_, v_a_2006_, v_snd_2001_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2026_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2026_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2026_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
if (lean_obj_tag(v_a_2008_) == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2012_, 0, v_a_2008_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2012_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_snd_2001_);
v___x_2014_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2014_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; 
lean_del_object(v___x_2010_);
lean_dec(v_snd_2001_);
v_a_2019_ = lean_ctor_get(v_a_2008_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v_a_2008_, 1);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_a_2019_);
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2021_ = v___x_2003_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_a_2019_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
size_t v___x_2022_; size_t v___x_2023_; 
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_1986_, v___x_2022_);
v_i_1986_ = v___x_2023_;
v_b_1987_ = v___x_2021_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_del_object(v___x_2003_);
lean_dec(v_snd_2001_);
v_a_2027_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2007_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2007_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2___boxed(lean_object* v_init_2037_, lean_object* v_as_2038_, lean_object* v_sz_2039_, lean_object* v_i_2040_, lean_object* v_b_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
size_t v_sz_boxed_2053_; size_t v_i_boxed_2054_; lean_object* v_res_2055_; 
v_sz_boxed_2053_ = lean_unbox_usize(v_sz_2039_);
lean_dec(v_sz_2039_);
v_i_boxed_2054_ = lean_unbox_usize(v_i_2040_);
lean_dec(v_i_2040_);
v_res_2055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_2037_, v_as_2038_, v_sz_boxed_2053_, v_i_boxed_2054_, v_b_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v_as_2038_);
lean_dec(v_init_2037_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1___boxed(lean_object* v_init_2056_, lean_object* v_n_2057_, lean_object* v_b_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2056_, v_n_2057_, v_b_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v_n_2057_);
lean_dec(v_init_2056_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(lean_object* v_as_2071_, size_t v_sz_2072_, size_t v_i_2073_, lean_object* v_b_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_usize_dec_lt(v_i_2073_, v_sz_2072_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_b_2074_);
return v___x_2087_;
}
else
{
lean_object* v_snd_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2147_; 
v_snd_2088_ = lean_ctor_get(v_b_2074_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_b_2074_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v_b_2074_, 0);
lean_dec(v_unused_2148_);
v___x_2090_ = v_b_2074_;
v_isShared_2091_ = v_isSharedCheck_2147_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_snd_2088_);
lean_dec(v_b_2074_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2147_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v_a_2094_; lean_object* v_a_2104_; 
v___x_2092_ = lean_box(0);
v_a_2104_ = lean_array_uget(v_as_2071_, v_i_2073_);
if (lean_obj_tag(v_a_2104_) == 1)
{
lean_object* v_val_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2146_; 
v_val_2105_ = lean_ctor_get(v_a_2104_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_a_2104_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2107_ = v_a_2104_;
v_isShared_2108_ = v_isSharedCheck_2146_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_val_2105_);
lean_dec(v_a_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2146_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v_d_2109_; lean_object* v_p_2110_; lean_object* v___x_2111_; 
v_d_2109_ = lean_ctor_get(v_val_2105_, 0);
lean_inc(v_d_2109_);
v_p_2110_ = lean_ctor_get(v_val_2105_, 1);
lean_inc_ref(v_p_2110_);
lean_dec(v_val_2105_);
v___x_2111_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_2110_, v_snd_2088_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec_ref(v_p_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
lean_dec_ref_known(v___x_2111_, 1);
v___x_2112_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2113_ = lean_int_dec_lt(v___x_2112_, v_d_2109_);
lean_dec(v_d_2109_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2115_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2114_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2129_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2129_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2129_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
if (lean_obj_tag(v_a_2116_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; 
lean_del_object(v___x_2090_);
v_a_2120_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v_a_2116_, 1);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v_a_2120_);
v___x_2122_ = v___x_2107_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2120_);
v___x_2122_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v_snd_2088_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2123_);
v___x_2125_ = v___x_2118_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
lean_object* v_a_2128_; 
lean_del_object(v___x_2118_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2088_);
v_a_2128_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v_a_2116_, 1);
v_a_2094_ = v_a_2128_;
goto v___jp_2093_;
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_2107_);
lean_del_object(v___x_2090_);
lean_dec(v_snd_2088_);
v_a_2130_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2115_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2115_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_del_object(v___x_2107_);
goto v___jp_2101_;
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_d_2109_);
lean_del_object(v___x_2107_);
lean_del_object(v___x_2090_);
lean_dec(v_snd_2088_);
v_a_2138_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2111_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2111_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
else
{
lean_dec(v_a_2104_);
goto v___jp_2101_;
}
v___jp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v_a_2094_);
lean_ctor_set(v___x_2090_, 0, v___x_2092_);
v___x_2096_ = v___x_2090_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_a_2094_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
size_t v___x_2097_; size_t v___x_2098_; 
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_i_2073_, v___x_2097_);
v_i_2073_ = v___x_2098_;
v_b_2074_ = v___x_2096_;
goto _start;
}
}
v___jp_2101_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_unsigned_to_nat(1u);
v___x_2103_ = lean_nat_add(v_snd_2088_, v___x_2102_);
lean_dec(v_snd_2088_);
v_a_2094_ = v___x_2103_;
goto v___jp_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2149_, lean_object* v_sz_2150_, lean_object* v_i_2151_, lean_object* v_b_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
size_t v_sz_boxed_2164_; size_t v_i_boxed_2165_; lean_object* v_res_2166_; 
v_sz_boxed_2164_ = lean_unbox_usize(v_sz_2150_);
lean_dec(v_sz_2150_);
v_i_boxed_2165_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2149_, v_sz_boxed_2164_, v_i_boxed_2165_, v_b_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v_as_2149_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(lean_object* v_as_2167_, size_t v_sz_2168_, size_t v_i_2169_, lean_object* v_b_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_usize_dec_lt(v_i_2169_, v_sz_2168_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_b_2170_);
return v___x_2183_;
}
else
{
lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2243_; 
v_snd_2184_ = lean_ctor_get(v_b_2170_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_b_2170_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v_b_2170_, 0);
lean_dec(v_unused_2244_);
v___x_2186_ = v_b_2170_;
v_isShared_2187_ = v_isSharedCheck_2243_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_dec(v_b_2170_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2243_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v_a_2190_; lean_object* v_a_2200_; 
v___x_2188_ = lean_box(0);
v_a_2200_ = lean_array_uget(v_as_2167_, v_i_2169_);
if (lean_obj_tag(v_a_2200_) == 1)
{
lean_object* v_val_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2242_; 
v_val_2201_ = lean_ctor_get(v_a_2200_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2200_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2203_ = v_a_2200_;
v_isShared_2204_ = v_isSharedCheck_2242_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_val_2201_);
lean_dec(v_a_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2242_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v_d_2205_; lean_object* v_p_2206_; lean_object* v___x_2207_; 
v_d_2205_ = lean_ctor_get(v_val_2201_, 0);
lean_inc(v_d_2205_);
v_p_2206_ = lean_ctor_get(v_val_2201_, 1);
lean_inc_ref(v_p_2206_);
lean_dec(v_val_2201_);
v___x_2207_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_2206_, v_snd_2184_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec_ref(v_p_2206_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v___x_2208_; uint8_t v___x_2209_; 
lean_dec_ref_known(v___x_2207_, 1);
v___x_2208_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2209_ = lean_int_dec_lt(v___x_2208_, v_d_2205_);
lean_dec(v_d_2205_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2211_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2210_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2225_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2225_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2225_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
if (lean_obj_tag(v_a_2212_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; 
lean_del_object(v___x_2186_);
v_a_2216_ = lean_ctor_get(v_a_2212_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v_a_2212_, 1);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v_a_2216_);
v___x_2218_ = v___x_2203_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2216_);
v___x_2218_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v_snd_2184_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2219_);
v___x_2221_ = v___x_2214_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
else
{
lean_object* v_a_2224_; 
lean_del_object(v___x_2214_);
lean_del_object(v___x_2203_);
lean_dec(v_snd_2184_);
v_a_2224_ = lean_ctor_get(v_a_2212_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v_a_2212_, 1);
v_a_2190_ = v_a_2224_;
goto v___jp_2189_;
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_del_object(v___x_2203_);
lean_del_object(v___x_2186_);
lean_dec(v_snd_2184_);
v_a_2226_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2211_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2211_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_del_object(v___x_2203_);
goto v___jp_2197_;
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_d_2205_);
lean_del_object(v___x_2203_);
lean_del_object(v___x_2186_);
lean_dec(v_snd_2184_);
v_a_2234_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2207_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2207_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
else
{
lean_dec(v_a_2200_);
goto v___jp_2197_;
}
v___jp_2189_:
{
lean_object* v___x_2192_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v_a_2190_);
lean_ctor_set(v___x_2186_, 0, v___x_2188_);
v___x_2192_ = v___x_2186_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_a_2190_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2169_, v___x_2193_);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2167_, v_sz_2168_, v___x_2194_, v___x_2192_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
return v___x_2195_;
}
}
v___jp_2197_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_add(v_snd_2184_, v___x_2198_);
lean_dec(v_snd_2184_);
v_a_2190_ = v___x_2199_;
goto v___jp_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2___boxed(lean_object* v_as_2245_, lean_object* v_sz_2246_, lean_object* v_i_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
size_t v_sz_boxed_2260_; size_t v_i_boxed_2261_; lean_object* v_res_2262_; 
v_sz_boxed_2260_ = lean_unbox_usize(v_sz_2246_);
lean_dec(v_sz_2246_);
v_i_boxed_2261_ = lean_unbox_usize(v_i_2247_);
lean_dec(v_i_2247_);
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_as_2245_, v_sz_boxed_2260_, v_i_boxed_2261_, v_b_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v_as_2245_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(lean_object* v_t_2263_, lean_object* v_init_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_root_2276_; lean_object* v_tail_2277_; lean_object* v___x_2278_; 
v_root_2276_ = lean_ctor_get(v_t_2263_, 0);
v_tail_2277_ = lean_ctor_get(v_t_2263_, 1);
lean_inc(v_init_2264_);
v___x_2278_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2264_, v_root_2276_, v_init_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v_init_2264_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2315_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2315_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2315_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
if (lean_obj_tag(v_a_2279_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; 
v_a_2283_ = lean_ctor_get(v_a_2279_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v_a_2279_, 1);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v_a_2283_);
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; size_t v_sz_2290_; size_t v___x_2291_; lean_object* v___x_2292_; 
lean_del_object(v___x_2281_);
v_a_2287_ = lean_ctor_get(v_a_2279_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v_a_2279_, 1);
v___x_2288_ = lean_box(0);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
lean_ctor_set(v___x_2289_, 1, v_a_2287_);
v_sz_2290_ = lean_array_size(v_tail_2277_);
v___x_2291_ = ((size_t)0ULL);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_tail_2277_, v_sz_2290_, v___x_2291_, v___x_2289_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2306_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2306_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2306_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_fst_2297_; 
v_fst_2297_ = lean_ctor_get(v_a_2293_, 0);
if (lean_obj_tag(v_fst_2297_) == 0)
{
lean_object* v_snd_2298_; lean_object* v___x_2300_; 
v_snd_2298_ = lean_ctor_get(v_a_2293_, 1);
lean_inc(v_snd_2298_);
lean_dec(v_a_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v_snd_2298_);
v___x_2300_ = v___x_2295_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_snd_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
else
{
lean_object* v_val_2302_; lean_object* v___x_2304_; 
lean_inc_ref(v_fst_2297_);
lean_dec(v_a_2293_);
v_val_2302_ = lean_ctor_get(v_fst_2297_, 0);
lean_inc(v_val_2302_);
lean_dec_ref_known(v_fst_2297_, 1);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v_val_2302_);
v___x_2304_ = v___x_2295_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_val_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v_a_2307_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2292_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2292_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
v_a_2316_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2278_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2278_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1___boxed(lean_object* v_t_2324_, lean_object* v_init_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_t_2324_, v_init_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v_t_2324_);
return v_res_2337_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2339_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0));
v___x_2340_ = lean_unsigned_to_nat(2u);
v___x_2341_ = lean_unsigned_to_nat(65u);
v___x_2342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_2343_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2344_ = l_mkPanicMessageWithDecl(v___x_2343_, v___x_2342_, v___x_2341_, v___x_2340_, v___x_2339_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2345_, v_a_2353_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v_vars_2358_; lean_object* v_dvds_2359_; lean_object* v_size_2360_; lean_object* v_size_2361_; uint8_t v___x_2362_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v_vars_2358_ = lean_ctor_get(v_a_2357_, 0);
lean_inc_ref(v_vars_2358_);
v_dvds_2359_ = lean_ctor_get(v_a_2357_, 5);
lean_inc_ref(v_dvds_2359_);
lean_dec(v_a_2357_);
v_size_2360_ = lean_ctor_get(v_vars_2358_, 2);
lean_inc(v_size_2360_);
lean_dec_ref(v_vars_2358_);
v_size_2361_ = lean_ctor_get(v_dvds_2359_, 2);
v___x_2362_ = lean_nat_dec_eq(v_size_2360_, v_size_2361_);
lean_dec(v_size_2360_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v_dvds_2359_);
v___x_2363_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1);
v___x_2364_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2363_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_unsigned_to_nat(0u);
v___x_2366_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_dvds_2359_, v___x_2365_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
lean_dec_ref(v_dvds_2359_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2374_; 
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v___x_2366_, 0);
lean_dec(v_unused_2375_);
v___x_2368_ = v___x_2366_;
v_isShared_2369_ = v_isSharedCheck_2374_;
goto v_resetjp_2367_;
}
else
{
lean_dec(v___x_2366_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2374_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2370_ = lean_box(0);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2370_);
v___x_2372_ = v___x_2368_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
v_a_2376_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2366_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2366_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
v_a_2384_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2356_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2356_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___boxed(lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec(v_a_2393_);
lean_dec(v_a_2392_);
return v_res_2403_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2405_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_2406_ = lean_unsigned_to_nat(6u);
v___x_2407_ = lean_unsigned_to_nat(81u);
v___x_2408_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2409_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2410_ = l_mkPanicMessageWithDecl(v___x_2409_, v___x_2408_, v___x_2407_, v___x_2406_, v___x_2405_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2412_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2));
v___x_2413_ = lean_unsigned_to_nat(6u);
v___x_2414_ = lean_unsigned_to_nat(79u);
v___x_2415_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2416_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2417_ = l_mkPanicMessageWithDecl(v___x_2416_, v___x_2415_, v___x_2414_, v___x_2413_, v___x_2412_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(lean_object* v_vars_2418_, lean_object* v___x_2419_, lean_object* v_x_2420_, lean_object* v_____s_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_fst_2438_; lean_object* v_snd_2439_; lean_object* v_size_2440_; uint8_t v___x_2441_; 
v_fst_2438_ = lean_ctor_get(v_x_2420_, 0);
v_snd_2439_ = lean_ctor_get(v_x_2420_, 1);
v_size_2440_ = lean_ctor_get(v_vars_2418_, 2);
v___x_2441_ = lean_nat_dec_lt(v_snd_2439_, v_size_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1);
v___x_2443_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2442_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_dec_ref_known(v___x_2443_, 1);
goto v___jp_2433_;
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v___x_2452_; size_t v___x_2453_; size_t v___x_2454_; uint8_t v___x_2455_; 
v___x_2452_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2419_, v_vars_2418_, v_snd_2439_);
v___x_2453_ = lean_ptr_addr(v_fst_2438_);
v___x_2454_ = lean_ptr_addr(v___x_2452_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_usize_dec_eq(v___x_2453_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3);
v___x_2457_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2456_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2457_;
}
else
{
goto v___jp_2433_;
}
}
v___jp_2433_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2434_ = lean_unsigned_to_nat(1u);
v___x_2435_ = lean_nat_add(v_____s_2421_, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(lean_object* v_vars_2458_, lean_object* v___x_2459_, lean_object* v_x_2460_, lean_object* v_____s_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(v_vars_2458_, v___x_2459_, v_x_2460_, v_____s_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec(v_____s_2461_);
lean_dec_ref(v_x_2460_);
lean_dec_ref(v___x_2459_);
lean_dec_ref(v_vars_2458_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2474_, lean_object* v_keys_2475_, lean_object* v_vals_2476_, lean_object* v_i_2477_, lean_object* v_acc_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = lean_array_get_size(v_keys_2475_);
v___x_2491_ = lean_nat_dec_lt(v_i_2477_, v___x_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec(v_i_2477_);
lean_dec_ref(v_f_2474_);
v___x_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_acc_2478_);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
return v___x_2493_;
}
else
{
lean_object* v_k_2494_; lean_object* v_v_2495_; lean_object* v___x_2496_; 
v_k_2494_ = lean_array_fget_borrowed(v_keys_2475_, v_i_2477_);
v_v_2495_ = lean_array_fget_borrowed(v_vals_2476_, v_i_2477_);
lean_inc_ref(v_f_2474_);
lean_inc(v___y_2488_);
lean_inc_ref(v___y_2487_);
lean_inc(v___y_2486_);
lean_inc_ref(v___y_2485_);
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___y_2482_);
lean_inc_ref(v___y_2481_);
lean_inc(v___y_2480_);
lean_inc(v___y_2479_);
lean_inc(v_v_2495_);
lean_inc(v_k_2494_);
v___x_2496_ = lean_apply_14(v_f_2474_, v_acc_2478_, v_k_2494_, v_v_2495_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, lean_box(0));
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
if (lean_obj_tag(v_a_2497_) == 0)
{
lean_dec_ref_known(v_a_2497_, 1);
lean_dec(v_i_2477_);
lean_dec_ref(v_f_2474_);
return v___x_2496_;
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec_ref_known(v___x_2496_, 1);
v_a_2498_ = lean_ctor_get(v_a_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v_a_2497_, 1);
v___x_2499_ = lean_unsigned_to_nat(1u);
v___x_2500_ = lean_nat_add(v_i_2477_, v___x_2499_);
lean_dec(v_i_2477_);
v_i_2477_ = v___x_2500_;
v_acc_2478_ = v_a_2498_;
goto _start;
}
}
else
{
lean_dec(v_i_2477_);
lean_dec_ref(v_f_2474_);
return v___x_2496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2502_, lean_object* v_keys_2503_, lean_object* v_vals_2504_, lean_object* v_i_2505_, lean_object* v_acc_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2502_, v_keys_2503_, v_vals_2504_, v_i_2505_, v_acc_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v_vals_2504_);
lean_dec_ref(v_keys_2503_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2519_, lean_object* v_as_2520_, size_t v_i_2521_, size_t v_stop_2522_, lean_object* v_b_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_a_2536_; lean_object* v___y_2541_; uint8_t v___x_2544_; 
v___x_2544_ = lean_usize_dec_eq(v_i_2521_, v_stop_2522_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_array_uget_borrowed(v_as_2520_, v_i_2521_);
switch(lean_obj_tag(v___x_2545_))
{
case 0:
{
lean_object* v_key_2546_; lean_object* v_val_2547_; lean_object* v___x_2548_; 
v_key_2546_ = lean_ctor_get(v___x_2545_, 0);
v_val_2547_ = lean_ctor_get(v___x_2545_, 1);
lean_inc_ref(v_f_2519_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc(v_val_2547_);
lean_inc(v_key_2546_);
v___x_2548_ = lean_apply_14(v_f_2519_, v_b_2523_, v_key_2546_, v_val_2547_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
v___y_2541_ = v___x_2548_;
goto v___jp_2540_;
}
case 1:
{
lean_object* v_node_2549_; lean_object* v___x_2550_; 
v_node_2549_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_node_2549_);
lean_inc_ref(v_f_2519_);
v___x_2550_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2519_, v_node_2549_, v_b_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
v___y_2541_ = v___x_2550_;
goto v___jp_2540_;
}
default: 
{
v_a_2536_ = v_b_2523_;
goto v___jp_2535_;
}
}
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec_ref(v_f_2519_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_b_2523_);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
v___jp_2535_:
{
size_t v___x_2537_; size_t v___x_2538_; 
v___x_2537_ = ((size_t)1ULL);
v___x_2538_ = lean_usize_add(v_i_2521_, v___x_2537_);
v_i_2521_ = v___x_2538_;
v_b_2523_ = v_a_2536_;
goto _start;
}
v___jp_2540_:
{
if (lean_obj_tag(v___y_2541_) == 0)
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___y_2541_, 0);
if (lean_obj_tag(v_a_2542_) == 0)
{
lean_dec_ref(v_f_2519_);
return v___y_2541_;
}
else
{
lean_object* v_a_2543_; 
lean_inc_ref(v_a_2542_);
lean_dec_ref_known(v___y_2541_, 1);
v_a_2543_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v_a_2542_, 1);
v_a_2536_ = v_a_2543_;
goto v___jp_2535_;
}
}
else
{
lean_dec_ref(v_f_2519_);
return v___y_2541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_object* v_es_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2581_; 
v_es_2567_ = lean_ctor_get(v_x_2554_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_x_2554_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2569_ = v_x_2554_;
v_isShared_2570_ = v_isSharedCheck_2581_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_es_2567_);
lean_dec(v_x_2554_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2581_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = lean_array_get_size(v_es_2567_);
v___x_2573_ = lean_nat_dec_lt(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2575_; 
lean_dec_ref(v_es_2567_);
lean_dec_ref(v_f_2553_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set_tag(v___x_2569_, 1);
lean_ctor_set(v___x_2569_, 0, v_x_2555_);
v___x_2575_ = v___x_2569_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_x_2555_);
v___x_2575_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
}
else
{
size_t v___x_2578_; size_t v___x_2579_; lean_object* v___x_2580_; 
lean_del_object(v___x_2569_);
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = lean_usize_of_nat(v___x_2572_);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2553_, v_es_2567_, v___x_2578_, v___x_2579_, v_x_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec_ref(v_es_2567_);
return v___x_2580_;
}
}
}
else
{
lean_object* v_ks_2582_; lean_object* v_vs_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_ks_2582_ = lean_ctor_get(v_x_2554_, 0);
lean_inc_ref(v_ks_2582_);
v_vs_2583_ = lean_ctor_get(v_x_2554_, 1);
lean_inc_ref(v_vs_2583_);
lean_dec_ref_known(v_x_2554_, 2);
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2553_, v_ks_2582_, v_vs_2583_, v___x_2584_, v_x_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec_ref(v_vs_2583_);
lean_dec_ref(v_ks_2582_);
return v___x_2585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2586_, lean_object* v_x_2587_, lean_object* v_x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2586_, v_x_2587_, v_x_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec(v___y_2589_);
return v_res_2600_;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(lean_object* v_f_2620_, lean_object* v_s_2621_, lean_object* v_a_2622_, lean_object* v_b_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v_a_2622_);
lean_ctor_set(v___x_2635_, 1, v_b_2623_);
lean_inc(v___y_2633_);
lean_inc_ref(v___y_2632_);
lean_inc(v___y_2631_);
lean_inc_ref(v___y_2630_);
lean_inc(v___y_2629_);
lean_inc_ref(v___y_2628_);
lean_inc(v___y_2627_);
lean_inc_ref(v___y_2626_);
lean_inc(v___y_2625_);
lean_inc(v___y_2624_);
v___x_2636_ = lean_apply_13(v_f_2620_, v___x_2635_, v_s_2621_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, lean_box(0));
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2663_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2663_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2663_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
if (lean_obj_tag(v_a_2637_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2651_; 
v_a_2641_ = lean_ctor_get(v_a_2637_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2643_ = v_a_2637_;
v_isShared_2644_ = v_isSharedCheck_2651_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v_a_2637_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2651_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2648_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2646_);
v___x_2648_ = v___x_2639_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2662_; 
v_a_2652_ = lean_ctor_get(v_a_2637_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2654_ = v_a_2637_;
v_isShared_2655_ = v_isSharedCheck_2662_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v_a_2637_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2662_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2659_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2657_);
v___x_2659_ = v___x_2639_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
v_a_2664_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2636_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2636_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed(lean_object* v_f_2672_, lean_object* v_s_2673_, lean_object* v_a_2674_, lean_object* v_b_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(v_f_2672_, v_s_2673_, v_a_2674_, v_b_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec(v___y_2676_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(lean_object* v_map_2688_, lean_object* v_init_2689_, lean_object* v_f_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___f_2702_; lean_object* v___x_2703_; 
v___f_2702_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed), 15, 1);
lean_closure_set(v___f_2702_, 0, v_f_2690_);
lean_inc_ref(v_map_2688_);
v___x_2703_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v___f_2702_, v_map_2688_, v_init_2689_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2712_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v_a_2708_; lean_object* v___x_2710_; 
v_a_2708_ = lean_ctor_get(v_a_2704_, 0);
lean_inc(v_a_2708_);
lean_dec(v_a_2704_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v_a_2708_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2703_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2703_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___boxed(lean_object* v_map_2721_, lean_object* v_init_2722_, lean_object* v_f_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2721_, v_init_2722_, v_f_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v_map_2721_);
return v_res_2735_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2737_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0));
v___x_2738_ = lean_unsigned_to_nat(2u);
v___x_2739_ = lean_unsigned_to_nat(83u);
v___x_2740_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2741_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2742_ = l_mkPanicMessageWithDecl(v___x_2741_, v___x_2740_, v___x_2739_, v___x_2738_, v___x_2737_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars(lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = l_Lean_instInhabitedExpr;
v___x_2755_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2743_, v_a_2751_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v_vars_2757_; lean_object* v_varMap_2758_; lean_object* v___f_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v_vars_2757_ = lean_ctor_get(v_a_2756_, 0);
lean_inc_ref_n(v_vars_2757_, 2);
v_varMap_2758_ = lean_ctor_get(v_a_2756_, 1);
lean_inc_ref(v_varMap_2758_);
lean_dec(v_a_2756_);
v___f_2759_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed), 15, 2);
lean_closure_set(v___f_2759_, 0, v_vars_2757_);
lean_closure_set(v___f_2759_, 1, v___x_2754_);
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_varMap_2758_, v___x_2760_, v___f_2759_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec_ref(v_varMap_2758_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2774_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2774_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2774_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_size_2766_; uint8_t v___x_2767_; 
v_size_2766_ = lean_ctor_get(v_vars_2757_, 2);
lean_inc(v_size_2766_);
lean_dec_ref(v_vars_2757_);
v___x_2767_ = lean_nat_dec_eq(v_size_2766_, v_a_2762_);
lean_dec(v_a_2762_);
lean_dec(v_size_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_del_object(v___x_2764_);
v___x_2768_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1);
v___x_2769_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2768_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2770_ = lean_box(0);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2770_);
v___x_2772_ = v___x_2764_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec_ref(v_vars_2757_);
v_a_2775_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2761_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2761_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_a_2783_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2755_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2755_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___boxed(lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec(v_a_2791_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(lean_object* v_00_u03c3_2803_, lean_object* v_00_u03b2_2804_, lean_object* v_map_2805_, lean_object* v_init_2806_, lean_object* v_f_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2805_, v_init_2806_, v_f_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___boxed(lean_object* v_00_u03c3_2820_, lean_object* v_00_u03b2_2821_, lean_object* v_map_2822_, lean_object* v_init_2823_, lean_object* v_f_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(v_00_u03c3_2820_, v_00_u03b2_2821_, v_map_2822_, v_init_2823_, v_f_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v_map_2822_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(lean_object* v_map_2837_, lean_object* v_f_2838_, lean_object* v_init_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2838_, v_map_2837_, v_init_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_map_2852_, lean_object* v_f_2853_, lean_object* v_init_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(v_map_2852_, v_f_2853_, v_init_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v___y_2855_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(lean_object* v_00_u03c3_2867_, lean_object* v_00_u03c3_2868_, lean_object* v_00_u03b2_2869_, lean_object* v_map_2870_, lean_object* v_f_2871_, lean_object* v_init_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2871_, v_map_2870_, v_init_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_2885_ = _args[0];
lean_object* v_00_u03c3_2886_ = _args[1];
lean_object* v_00_u03b2_2887_ = _args[2];
lean_object* v_map_2888_ = _args[3];
lean_object* v_f_2889_ = _args[4];
lean_object* v_init_2890_ = _args[5];
lean_object* v___y_2891_ = _args[6];
lean_object* v___y_2892_ = _args[7];
lean_object* v___y_2893_ = _args[8];
lean_object* v___y_2894_ = _args[9];
lean_object* v___y_2895_ = _args[10];
lean_object* v___y_2896_ = _args[11];
lean_object* v___y_2897_ = _args[12];
lean_object* v___y_2898_ = _args[13];
lean_object* v___y_2899_ = _args[14];
lean_object* v___y_2900_ = _args[15];
lean_object* v___y_2901_ = _args[16];
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(v_00_u03c3_2885_, v_00_u03c3_2886_, v_00_u03b2_2887_, v_map_2888_, v_f_2889_, v_init_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec(v___y_2891_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2903_, lean_object* v_00_u03c3_2904_, lean_object* v_00_u03b1_2905_, lean_object* v_00_u03b2_2906_, lean_object* v_f_2907_, lean_object* v_x_2908_, lean_object* v_x_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2907_, v_x_2908_, v_x_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_2922_ = _args[0];
lean_object* v_00_u03c3_2923_ = _args[1];
lean_object* v_00_u03b1_2924_ = _args[2];
lean_object* v_00_u03b2_2925_ = _args[3];
lean_object* v_f_2926_ = _args[4];
lean_object* v_x_2927_ = _args[5];
lean_object* v_x_2928_ = _args[6];
lean_object* v___y_2929_ = _args[7];
lean_object* v___y_2930_ = _args[8];
lean_object* v___y_2931_ = _args[9];
lean_object* v___y_2932_ = _args[10];
lean_object* v___y_2933_ = _args[11];
lean_object* v___y_2934_ = _args[12];
lean_object* v___y_2935_ = _args[13];
lean_object* v___y_2936_ = _args[14];
lean_object* v___y_2937_ = _args[15];
lean_object* v___y_2938_ = _args[16];
lean_object* v___y_2939_ = _args[17];
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(v_00_u03c3_2922_, v_00_u03c3_2923_, v_00_u03b1_2924_, v_00_u03b2_2925_, v_f_2926_, v_x_2927_, v_x_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2941_, lean_object* v_00_u03b2_2942_, lean_object* v_00_u03c3_2943_, lean_object* v_00_u03c3_2944_, lean_object* v_f_2945_, lean_object* v_as_2946_, size_t v_i_2947_, size_t v_stop_2948_, lean_object* v_b_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2945_, v_as_2946_, v_i_2947_, v_stop_2948_, v_b_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03b1_2962_ = _args[0];
lean_object* v_00_u03b2_2963_ = _args[1];
lean_object* v_00_u03c3_2964_ = _args[2];
lean_object* v_00_u03c3_2965_ = _args[3];
lean_object* v_f_2966_ = _args[4];
lean_object* v_as_2967_ = _args[5];
lean_object* v_i_2968_ = _args[6];
lean_object* v_stop_2969_ = _args[7];
lean_object* v_b_2970_ = _args[8];
lean_object* v___y_2971_ = _args[9];
lean_object* v___y_2972_ = _args[10];
lean_object* v___y_2973_ = _args[11];
lean_object* v___y_2974_ = _args[12];
lean_object* v___y_2975_ = _args[13];
lean_object* v___y_2976_ = _args[14];
lean_object* v___y_2977_ = _args[15];
lean_object* v___y_2978_ = _args[16];
lean_object* v___y_2979_ = _args[17];
lean_object* v___y_2980_ = _args[18];
lean_object* v___y_2981_ = _args[19];
_start:
{
size_t v_i_boxed_2982_; size_t v_stop_boxed_2983_; lean_object* v_res_2984_; 
v_i_boxed_2982_ = lean_unbox_usize(v_i_2968_);
lean_dec(v_i_2968_);
v_stop_boxed_2983_ = lean_unbox_usize(v_stop_2969_);
lean_dec(v_stop_2969_);
v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2962_, v_00_u03b2_2963_, v_00_u03c3_2964_, v_00_u03c3_2965_, v_f_2966_, v_as_2967_, v_i_boxed_2982_, v_stop_boxed_2983_, v_b_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v_as_2967_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2985_, lean_object* v_00_u03c3_2986_, lean_object* v_00_u03b1_2987_, lean_object* v_00_u03b2_2988_, lean_object* v_f_2989_, lean_object* v_keys_2990_, lean_object* v_vals_2991_, lean_object* v_heq_2992_, lean_object* v_i_2993_, lean_object* v_acc_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2989_, v_keys_2990_, v_vals_2991_, v_i_2993_, v_acc_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_3007_ = _args[0];
lean_object* v_00_u03c3_3008_ = _args[1];
lean_object* v_00_u03b1_3009_ = _args[2];
lean_object* v_00_u03b2_3010_ = _args[3];
lean_object* v_f_3011_ = _args[4];
lean_object* v_keys_3012_ = _args[5];
lean_object* v_vals_3013_ = _args[6];
lean_object* v_heq_3014_ = _args[7];
lean_object* v_i_3015_ = _args[8];
lean_object* v_acc_3016_ = _args[9];
lean_object* v___y_3017_ = _args[10];
lean_object* v___y_3018_ = _args[11];
lean_object* v___y_3019_ = _args[12];
lean_object* v___y_3020_ = _args[13];
lean_object* v___y_3021_ = _args[14];
lean_object* v___y_3022_ = _args[15];
lean_object* v___y_3023_ = _args[16];
lean_object* v___y_3024_ = _args[17];
lean_object* v___y_3025_ = _args[18];
lean_object* v___y_3026_ = _args[19];
lean_object* v___y_3027_ = _args[20];
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3007_, v_00_u03c3_3008_, v_00_u03b1_3009_, v_00_u03b2_3010_, v_f_3011_, v_keys_3012_, v_vals_3013_, v_heq_3014_, v_i_3015_, v_acc_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v_vals_3013_);
lean_dec_ref(v_keys_3012_);
return v_res_3028_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(lean_object* v_a_3029_, lean_object* v_x_3030_){
_start:
{
if (lean_obj_tag(v_x_3030_) == 0)
{
uint8_t v___x_3031_; 
v___x_3031_ = 0;
return v___x_3031_;
}
else
{
lean_object* v_head_3032_; lean_object* v_tail_3033_; uint8_t v___x_3034_; 
v_head_3032_ = lean_ctor_get(v_x_3030_, 0);
v_tail_3033_ = lean_ctor_get(v_x_3030_, 1);
v___x_3034_ = lean_nat_dec_eq(v_a_3029_, v_head_3032_);
if (v___x_3034_ == 0)
{
v_x_3030_ = v_tail_3033_;
goto _start;
}
else
{
return v___x_3034_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0___boxed(lean_object* v_a_3036_, lean_object* v_x_3037_){
_start:
{
uint8_t v_res_3038_; lean_object* v_r_3039_; 
v_res_3038_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_a_3036_, v_x_3037_);
lean_dec(v_x_3037_);
lean_dec(v_a_3036_);
v_r_3039_ = lean_box(v_res_3038_);
return v_r_3039_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_3043_ = lean_unsigned_to_nat(6u);
v___x_3044_ = lean_unsigned_to_nat(91u);
v___x_3045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3046_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3047_ = l_mkPanicMessageWithDecl(v___x_3046_, v___x_3045_, v___x_3044_, v___x_3043_, v___x_3042_);
return v___x_3047_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3));
v___x_3050_ = lean_unsigned_to_nat(6u);
v___x_3051_ = lean_unsigned_to_nat(92u);
v___x_3052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3053_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3054_ = l_mkPanicMessageWithDecl(v___x_3053_, v___x_3052_, v___x_3051_, v___x_3050_, v___x_3049_);
return v___x_3054_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5));
v___x_3057_ = lean_unsigned_to_nat(6u);
v___x_3058_ = lean_unsigned_to_nat(93u);
v___x_3059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3060_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3061_ = l_mkPanicMessageWithDecl(v___x_3060_, v___x_3059_, v___x_3058_, v___x_3057_, v___x_3056_);
return v___x_3061_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7));
v___x_3064_ = lean_unsigned_to_nat(6u);
v___x_3065_ = lean_unsigned_to_nat(94u);
v___x_3066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3067_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3068_ = l_mkPanicMessageWithDecl(v___x_3067_, v___x_3066_, v___x_3065_, v___x_3064_, v___x_3063_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(lean_object* v_a_3069_, lean_object* v_as_3070_, size_t v_sz_3071_, size_t v_i_3072_, lean_object* v_b_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
uint8_t v___x_3085_; 
v___x_3085_ = lean_usize_dec_lt(v_i_3072_, v_sz_3071_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_b_3073_);
return v___x_3086_;
}
else
{
lean_object* v_snd_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3142_; 
v_snd_3087_ = lean_ctor_get(v_b_3073_, 1);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_b_3073_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; 
v_unused_3143_ = lean_ctor_get(v_b_3073_, 0);
lean_dec(v_unused_3143_);
v___x_3089_ = v_b_3073_;
v_isShared_3090_ = v_isSharedCheck_3142_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_snd_3087_);
lean_dec(v_b_3073_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3142_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v_a_3093_; lean_object* v___y_3104_; lean_object* v_a_3124_; 
v___x_3091_ = lean_box(0);
v_a_3124_ = lean_array_uget_borrowed(v_as_3070_, v_i_3072_);
if (lean_obj_tag(v_a_3124_) == 1)
{
lean_object* v_val_3125_; lean_object* v_p_3126_; uint8_t v___x_3127_; 
v_val_3125_ = lean_ctor_get(v_a_3124_, 0);
v_p_3126_ = lean_ctor_get(v_val_3125_, 0);
v___x_3127_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3129_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3128_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
v___y_3104_ = v___x_3129_;
goto v___jp_3103_;
}
else
{
uint8_t v___x_3130_; 
v___x_3130_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3126_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3132_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3131_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
v___y_3104_ = v___x_3132_;
goto v___jp_3103_;
}
else
{
lean_object* v_elimStack_3133_; uint8_t v___x_3134_; 
v_elimStack_3133_ = lean_ctor_get(v_a_3069_, 10);
v___x_3134_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3087_, v_elimStack_3133_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3136_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3135_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
v___y_3104_ = v___x_3136_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3137_ = l_Int_Internal_Linear_Poly_coeff(v_p_3126_, v_snd_3087_);
v___x_3138_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3139_ = lean_int_dec_eq(v___x_3137_, v___x_3138_);
lean_dec(v___x_3137_);
if (v___x_3139_ == 0)
{
goto v___jp_3100_;
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3141_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3140_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
v___y_3104_ = v___x_3141_;
goto v___jp_3103_;
}
}
}
}
}
else
{
goto v___jp_3100_;
}
v___jp_3092_:
{
lean_object* v___x_3095_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 1, v_a_3093_);
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3095_ = v___x_3089_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_a_3093_);
v___x_3095_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
size_t v___x_3096_; size_t v___x_3097_; 
v___x_3096_ = ((size_t)1ULL);
v___x_3097_ = lean_usize_add(v_i_3072_, v___x_3096_);
v_i_3072_ = v___x_3097_;
v_b_3073_ = v___x_3095_;
goto _start;
}
}
v___jp_3100_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_add(v_snd_3087_, v___x_3101_);
lean_dec(v_snd_3087_);
v_a_3093_ = v___x_3102_;
goto v___jp_3092_;
}
v___jp_3103_:
{
if (lean_obj_tag(v___y_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3115_; 
v_a_3105_ = lean_ctor_get(v___y_3104_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___y_3104_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3107_ = v___y_3104_;
v_isShared_3108_ = v_isSharedCheck_3115_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___y_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3115_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
if (lean_obj_tag(v_a_3105_) == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
lean_del_object(v___x_3089_);
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v_a_3105_);
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v_snd_3087_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3110_);
v___x_3112_ = v___x_3107_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
else
{
lean_object* v_a_3114_; 
lean_del_object(v___x_3107_);
lean_dec(v_snd_3087_);
v_a_3114_ = lean_ctor_get(v_a_3105_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v_a_3105_, 1);
v_a_3093_ = v_a_3114_;
goto v___jp_3092_;
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_del_object(v___x_3089_);
lean_dec(v_snd_3087_);
v_a_3116_ = lean_ctor_get(v___y_3104_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___y_3104_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___y_3104_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___y_3104_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_a_3144_, lean_object* v_as_3145_, lean_object* v_sz_3146_, lean_object* v_i_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
size_t v_sz_boxed_3160_; size_t v_i_boxed_3161_; lean_object* v_res_3162_; 
v_sz_boxed_3160_ = lean_unbox_usize(v_sz_3146_);
lean_dec(v_sz_3146_);
v_i_boxed_3161_ = lean_unbox_usize(v_i_3147_);
lean_dec(v_i_3147_);
v_res_3162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3144_, v_as_3145_, v_sz_boxed_3160_, v_i_boxed_3161_, v_b_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v_as_3145_);
lean_dec_ref(v_a_3144_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(lean_object* v_a_3163_, lean_object* v_as_3164_, size_t v_sz_3165_, size_t v_i_3166_, lean_object* v_b_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_usize_dec_lt(v_i_3166_, v_sz_3165_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v_b_3167_);
return v___x_3180_;
}
else
{
lean_object* v_snd_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3236_; 
v_snd_3181_ = lean_ctor_get(v_b_3167_, 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_b_3167_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_b_3167_, 0);
lean_dec(v_unused_3237_);
v___x_3183_ = v_b_3167_;
v_isShared_3184_ = v_isSharedCheck_3236_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_snd_3181_);
lean_dec(v_b_3167_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3236_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v_a_3187_; lean_object* v___y_3198_; lean_object* v_a_3218_; 
v___x_3185_ = lean_box(0);
v_a_3218_ = lean_array_uget_borrowed(v_as_3164_, v_i_3166_);
if (lean_obj_tag(v_a_3218_) == 1)
{
lean_object* v_val_3219_; lean_object* v_p_3220_; uint8_t v___x_3221_; 
v_val_3219_ = lean_ctor_get(v_a_3218_, 0);
v_p_3220_ = lean_ctor_get(v_val_3219_, 0);
v___x_3221_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3223_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3222_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
v___y_3198_ = v___x_3223_;
goto v___jp_3197_;
}
else
{
uint8_t v___x_3224_; 
v___x_3224_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3220_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3226_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3225_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
v___y_3198_ = v___x_3226_;
goto v___jp_3197_;
}
else
{
lean_object* v_elimStack_3227_; uint8_t v___x_3228_; 
v_elimStack_3227_ = lean_ctor_get(v_a_3163_, 10);
v___x_3228_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3181_, v_elimStack_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3230_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3229_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
v___y_3198_ = v___x_3230_;
goto v___jp_3197_;
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3231_ = l_Int_Internal_Linear_Poly_coeff(v_p_3220_, v_snd_3181_);
v___x_3232_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3233_ = lean_int_dec_eq(v___x_3231_, v___x_3232_);
lean_dec(v___x_3231_);
if (v___x_3233_ == 0)
{
goto v___jp_3194_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3235_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3234_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
v___y_3198_ = v___x_3235_;
goto v___jp_3197_;
}
}
}
}
}
else
{
goto v___jp_3194_;
}
v___jp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 1, v_a_3187_);
lean_ctor_set(v___x_3183_, 0, v___x_3185_);
v___x_3189_ = v___x_3183_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_a_3187_);
v___x_3189_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
size_t v___x_3190_; size_t v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_add(v_i_3166_, v___x_3190_);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3163_, v_as_3164_, v_sz_3165_, v___x_3191_, v___x_3189_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
return v___x_3192_;
}
}
v___jp_3194_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_unsigned_to_nat(1u);
v___x_3196_ = lean_nat_add(v_snd_3181_, v___x_3195_);
lean_dec(v_snd_3181_);
v_a_3187_ = v___x_3196_;
goto v___jp_3186_;
}
v___jp_3197_:
{
if (lean_obj_tag(v___y_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3209_; 
v_a_3199_ = lean_ctor_get(v___y_3198_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___y_3198_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3201_ = v___y_3198_;
v_isShared_3202_ = v_isSharedCheck_3209_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___y_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3209_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
if (lean_obj_tag(v_a_3199_) == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3206_; 
lean_del_object(v___x_3183_);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_a_3199_);
v___x_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v_snd_3181_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3204_);
v___x_3206_ = v___x_3201_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
else
{
lean_object* v_a_3208_; 
lean_del_object(v___x_3201_);
lean_dec(v_snd_3181_);
v_a_3208_ = lean_ctor_get(v_a_3199_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v_a_3199_, 1);
v_a_3187_ = v_a_3208_;
goto v___jp_3186_;
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3210_ = lean_ctor_get(v___y_3198_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___y_3198_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___y_3198_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___y_3198_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3___boxed(lean_object* v_a_3238_, lean_object* v_as_3239_, lean_object* v_sz_3240_, lean_object* v_i_3241_, lean_object* v_b_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
size_t v_sz_boxed_3254_; size_t v_i_boxed_3255_; lean_object* v_res_3256_; 
v_sz_boxed_3254_ = lean_unbox_usize(v_sz_3240_);
lean_dec(v_sz_3240_);
v_i_boxed_3255_ = lean_unbox_usize(v_i_3241_);
lean_dec(v_i_3241_);
v_res_3256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3238_, v_as_3239_, v_sz_boxed_3254_, v_i_boxed_3255_, v_b_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v_as_3239_);
lean_dec_ref(v_a_3238_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(lean_object* v_init_3257_, lean_object* v_a_3258_, lean_object* v_n_3259_, lean_object* v_b_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
if (lean_obj_tag(v_n_3259_) == 0)
{
lean_object* v_cs_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; size_t v_sz_3275_; size_t v___x_3276_; lean_object* v___x_3277_; 
v_cs_3272_ = lean_ctor_get(v_n_3259_, 0);
v___x_3273_ = lean_box(0);
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
lean_ctor_set(v___x_3274_, 1, v_b_3260_);
v_sz_3275_ = lean_array_size(v_cs_3272_);
v___x_3276_ = ((size_t)0ULL);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3257_, v_a_3258_, v_cs_3272_, v_sz_3275_, v___x_3276_, v___x_3274_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3292_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3292_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3292_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v_fst_3282_; 
v_fst_3282_ = lean_ctor_get(v_a_3278_, 0);
if (lean_obj_tag(v_fst_3282_) == 0)
{
lean_object* v_snd_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v_snd_3283_ = lean_ctor_get(v_a_3278_, 1);
lean_inc(v_snd_3283_);
lean_dec(v_a_3278_);
v___x_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3284_, 0, v_snd_3283_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3284_);
v___x_3286_ = v___x_3280_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
else
{
lean_object* v_val_3288_; lean_object* v___x_3290_; 
lean_inc_ref(v_fst_3282_);
lean_dec(v_a_3278_);
v_val_3288_ = lean_ctor_get(v_fst_3282_, 0);
lean_inc(v_val_3288_);
lean_dec_ref_known(v_fst_3282_, 1);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v_val_3288_);
v___x_3290_ = v___x_3280_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_val_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
v_a_3293_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3277_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3277_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
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
lean_object* v_vs_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; size_t v_sz_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v_vs_3301_ = lean_ctor_get(v_n_3259_, 0);
v___x_3302_ = lean_box(0);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v_b_3260_);
v_sz_3304_ = lean_array_size(v_vs_3301_);
v___x_3305_ = ((size_t)0ULL);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3258_, v_vs_3301_, v_sz_3304_, v___x_3305_, v___x_3303_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3321_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3321_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3321_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v_fst_3311_; 
v_fst_3311_ = lean_ctor_get(v_a_3307_, 0);
if (lean_obj_tag(v_fst_3311_) == 0)
{
lean_object* v_snd_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v_snd_3312_ = lean_ctor_get(v_a_3307_, 1);
lean_inc(v_snd_3312_);
lean_dec(v_a_3307_);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v_snd_3312_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3313_);
v___x_3315_ = v___x_3309_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
else
{
lean_object* v_val_3317_; lean_object* v___x_3319_; 
lean_inc_ref(v_fst_3311_);
lean_dec(v_a_3307_);
v_val_3317_ = lean_ctor_get(v_fst_3311_, 0);
lean_inc(v_val_3317_);
lean_dec_ref_known(v_fst_3311_, 1);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v_val_3317_);
v___x_3319_ = v___x_3309_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_val_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
v_a_3322_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3306_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3306_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(lean_object* v_init_3330_, lean_object* v_a_3331_, lean_object* v_as_3332_, size_t v_sz_3333_, size_t v_i_3334_, lean_object* v_b_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
uint8_t v___x_3347_; 
v___x_3347_ = lean_usize_dec_lt(v_i_3334_, v_sz_3333_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v_b_3335_);
return v___x_3348_;
}
else
{
lean_object* v_snd_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3383_; 
v_snd_3349_ = lean_ctor_get(v_b_3335_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_b_3335_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; 
v_unused_3384_ = lean_ctor_get(v_b_3335_, 0);
lean_dec(v_unused_3384_);
v___x_3351_ = v_b_3335_;
v_isShared_3352_ = v_isSharedCheck_3383_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_snd_3349_);
lean_dec(v_b_3335_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3383_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; lean_object* v_a_3354_; lean_object* v___x_3355_; 
v___x_3353_ = lean_box(0);
v_a_3354_ = lean_array_uget_borrowed(v_as_3332_, v_i_3334_);
lean_inc(v_snd_3349_);
v___x_3355_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3330_, v_a_3331_, v_a_3354_, v_snd_3349_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3374_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3374_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3374_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
if (lean_obj_tag(v_a_3356_) == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_a_3356_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3360_);
v___x_3362_ = v___x_3351_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_snd_3349_);
v___x_3362_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3362_);
v___x_3364_ = v___x_3358_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; 
lean_del_object(v___x_3358_);
lean_dec(v_snd_3349_);
v_a_3367_ = lean_ctor_get(v_a_3356_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v_a_3356_, 1);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 1, v_a_3367_);
lean_ctor_set(v___x_3351_, 0, v___x_3353_);
v___x_3369_ = v___x_3351_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_a_3367_);
v___x_3369_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
size_t v___x_3370_; size_t v___x_3371_; 
v___x_3370_ = ((size_t)1ULL);
v___x_3371_ = lean_usize_add(v_i_3334_, v___x_3370_);
v_i_3334_ = v___x_3371_;
v_b_3335_ = v___x_3369_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_del_object(v___x_3351_);
lean_dec(v_snd_3349_);
v_a_3375_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3355_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3355_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_3385_ = _args[0];
lean_object* v_a_3386_ = _args[1];
lean_object* v_as_3387_ = _args[2];
lean_object* v_sz_3388_ = _args[3];
lean_object* v_i_3389_ = _args[4];
lean_object* v_b_3390_ = _args[5];
lean_object* v___y_3391_ = _args[6];
lean_object* v___y_3392_ = _args[7];
lean_object* v___y_3393_ = _args[8];
lean_object* v___y_3394_ = _args[9];
lean_object* v___y_3395_ = _args[10];
lean_object* v___y_3396_ = _args[11];
lean_object* v___y_3397_ = _args[12];
lean_object* v___y_3398_ = _args[13];
lean_object* v___y_3399_ = _args[14];
lean_object* v___y_3400_ = _args[15];
lean_object* v___y_3401_ = _args[16];
_start:
{
size_t v_sz_boxed_3402_; size_t v_i_boxed_3403_; lean_object* v_res_3404_; 
v_sz_boxed_3402_ = lean_unbox_usize(v_sz_3388_);
lean_dec(v_sz_3388_);
v_i_boxed_3403_ = lean_unbox_usize(v_i_3389_);
lean_dec(v_i_3389_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3385_, v_a_3386_, v_as_3387_, v_sz_boxed_3402_, v_i_boxed_3403_, v_b_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v_as_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_init_3385_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1___boxed(lean_object* v_init_3405_, lean_object* v_a_3406_, lean_object* v_n_3407_, lean_object* v_b_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3405_, v_a_3406_, v_n_3407_, v_b_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v_n_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_init_3405_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(lean_object* v_a_3421_, lean_object* v_as_3422_, size_t v_sz_3423_, size_t v_i_3424_, lean_object* v_b_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
uint8_t v___x_3437_; 
v___x_3437_ = lean_usize_dec_lt(v_i_3424_, v_sz_3423_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3438_, 0, v_b_3425_);
return v___x_3438_;
}
else
{
lean_object* v_snd_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3501_; 
v_snd_3439_ = lean_ctor_get(v_b_3425_, 1);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_b_3425_);
if (v_isSharedCheck_3501_ == 0)
{
lean_object* v_unused_3502_; 
v_unused_3502_ = lean_ctor_get(v_b_3425_, 0);
lean_dec(v_unused_3502_);
v___x_3441_ = v_b_3425_;
v_isShared_3442_ = v_isSharedCheck_3501_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_snd_3439_);
lean_dec(v_b_3425_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3501_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v_a_3445_; lean_object* v___y_3456_; lean_object* v_a_3483_; 
v___x_3443_ = lean_box(0);
v_a_3483_ = lean_array_uget_borrowed(v_as_3422_, v_i_3424_);
if (lean_obj_tag(v_a_3483_) == 1)
{
lean_object* v_val_3484_; lean_object* v_p_3485_; uint8_t v___x_3486_; 
v_val_3484_ = lean_ctor_get(v_a_3483_, 0);
v_p_3485_ = lean_ctor_get(v_val_3484_, 0);
v___x_3486_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3485_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3488_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3487_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
v___y_3456_ = v___x_3488_;
goto v___jp_3455_;
}
else
{
uint8_t v___x_3489_; 
v___x_3489_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3485_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3491_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3490_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
v___y_3456_ = v___x_3491_;
goto v___jp_3455_;
}
else
{
lean_object* v_elimStack_3492_; uint8_t v___x_3493_; 
v_elimStack_3492_ = lean_ctor_get(v_a_3421_, 10);
v___x_3493_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3439_, v_elimStack_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3495_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3494_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
v___y_3456_ = v___x_3495_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3496_ = l_Int_Internal_Linear_Poly_coeff(v_p_3485_, v_snd_3439_);
v___x_3497_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3498_ = lean_int_dec_eq(v___x_3496_, v___x_3497_);
lean_dec(v___x_3496_);
if (v___x_3498_ == 0)
{
goto v___jp_3452_;
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3500_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3499_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
v___y_3456_ = v___x_3500_;
goto v___jp_3455_;
}
}
}
}
}
else
{
goto v___jp_3452_;
}
v___jp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v_a_3445_);
lean_ctor_set(v___x_3441_, 0, v___x_3443_);
v___x_3447_ = v___x_3441_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_a_3445_);
v___x_3447_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
size_t v___x_3448_; size_t v___x_3449_; 
v___x_3448_ = ((size_t)1ULL);
v___x_3449_ = lean_usize_add(v_i_3424_, v___x_3448_);
v_i_3424_ = v___x_3449_;
v_b_3425_ = v___x_3447_;
goto _start;
}
}
v___jp_3452_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3453_ = lean_unsigned_to_nat(1u);
v___x_3454_ = lean_nat_add(v_snd_3439_, v___x_3453_);
lean_dec(v_snd_3439_);
v_a_3445_ = v___x_3454_;
goto v___jp_3444_;
}
v___jp_3455_:
{
if (lean_obj_tag(v___y_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3474_; 
v_a_3457_ = lean_ctor_get(v___y_3456_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___y_3456_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3459_ = v___y_3456_;
v_isShared_3460_ = v_isSharedCheck_3474_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___y_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3474_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
if (lean_obj_tag(v_a_3457_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3472_; 
lean_del_object(v___x_3441_);
v_a_3461_ = lean_ctor_get(v_a_3457_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_a_3457_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3463_ = v_a_3457_;
v_isShared_3464_ = v_isSharedCheck_3472_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v_a_3457_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3472_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set_tag(v___x_3463_, 1);
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
lean_ctor_set(v___x_3467_, 1, v_snd_3439_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3467_);
v___x_3469_ = v___x_3459_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3473_; 
lean_del_object(v___x_3459_);
lean_dec(v_snd_3439_);
v_a_3473_ = lean_ctor_get(v_a_3457_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v_a_3457_, 1);
v_a_3445_ = v_a_3473_;
goto v___jp_3444_;
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_del_object(v___x_3441_);
lean_dec(v_snd_3439_);
v_a_3475_ = lean_ctor_get(v___y_3456_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___y_3456_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___y_3456_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___y_3456_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5___boxed(lean_object* v_a_3503_, lean_object* v_as_3504_, lean_object* v_sz_3505_, lean_object* v_i_3506_, lean_object* v_b_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
size_t v_sz_boxed_3519_; size_t v_i_boxed_3520_; lean_object* v_res_3521_; 
v_sz_boxed_3519_ = lean_unbox_usize(v_sz_3505_);
lean_dec(v_sz_3505_);
v_i_boxed_3520_ = lean_unbox_usize(v_i_3506_);
lean_dec(v_i_3506_);
v_res_3521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3503_, v_as_3504_, v_sz_boxed_3519_, v_i_boxed_3520_, v_b_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v_as_3504_);
lean_dec_ref(v_a_3503_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(lean_object* v_a_3522_, lean_object* v_as_3523_, size_t v_sz_3524_, size_t v_i_3525_, lean_object* v_b_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
uint8_t v___x_3538_; 
v___x_3538_ = lean_usize_dec_lt(v_i_3525_, v_sz_3524_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
v___x_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3539_, 0, v_b_3526_);
return v___x_3539_;
}
else
{
lean_object* v_snd_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3602_; 
v_snd_3540_ = lean_ctor_get(v_b_3526_, 1);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_b_3526_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; 
v_unused_3603_ = lean_ctor_get(v_b_3526_, 0);
lean_dec(v_unused_3603_);
v___x_3542_ = v_b_3526_;
v_isShared_3543_ = v_isSharedCheck_3602_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_snd_3540_);
lean_dec(v_b_3526_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3602_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v_a_3546_; lean_object* v___y_3557_; lean_object* v_a_3584_; 
v___x_3544_ = lean_box(0);
v_a_3584_ = lean_array_uget_borrowed(v_as_3523_, v_i_3525_);
if (lean_obj_tag(v_a_3584_) == 1)
{
lean_object* v_val_3585_; lean_object* v_p_3586_; uint8_t v___x_3587_; 
v_val_3585_ = lean_ctor_get(v_a_3584_, 0);
v_p_3586_ = lean_ctor_get(v_val_3585_, 0);
v___x_3587_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3586_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3589_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3588_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
v___y_3557_ = v___x_3589_;
goto v___jp_3556_;
}
else
{
uint8_t v___x_3590_; 
v___x_3590_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3586_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3592_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3591_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
v___y_3557_ = v___x_3592_;
goto v___jp_3556_;
}
else
{
lean_object* v_elimStack_3593_; uint8_t v___x_3594_; 
v_elimStack_3593_ = lean_ctor_get(v_a_3522_, 10);
v___x_3594_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3540_, v_elimStack_3593_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3596_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3595_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
v___y_3557_ = v___x_3596_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3597_ = l_Int_Internal_Linear_Poly_coeff(v_p_3586_, v_snd_3540_);
v___x_3598_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3599_ = lean_int_dec_eq(v___x_3597_, v___x_3598_);
lean_dec(v___x_3597_);
if (v___x_3599_ == 0)
{
goto v___jp_3553_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3601_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3600_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
v___y_3557_ = v___x_3601_;
goto v___jp_3556_;
}
}
}
}
}
else
{
goto v___jp_3553_;
}
v___jp_3545_:
{
lean_object* v___x_3548_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v_a_3546_);
lean_ctor_set(v___x_3542_, 0, v___x_3544_);
v___x_3548_ = v___x_3542_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3546_);
v___x_3548_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
size_t v___x_3549_; size_t v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((size_t)1ULL);
v___x_3550_ = lean_usize_add(v_i_3525_, v___x_3549_);
v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3522_, v_as_3523_, v_sz_3524_, v___x_3550_, v___x_3548_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
return v___x_3551_;
}
}
v___jp_3553_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = lean_unsigned_to_nat(1u);
v___x_3555_ = lean_nat_add(v_snd_3540_, v___x_3554_);
lean_dec(v_snd_3540_);
v_a_3546_ = v___x_3555_;
goto v___jp_3545_;
}
v___jp_3556_:
{
if (lean_obj_tag(v___y_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3575_; 
v_a_3558_ = lean_ctor_get(v___y_3557_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___y_3557_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3560_ = v___y_3557_;
v_isShared_3561_ = v_isSharedCheck_3575_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___y_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3575_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
if (lean_obj_tag(v_a_3558_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3573_; 
lean_del_object(v___x_3542_);
v_a_3562_ = lean_ctor_get(v_a_3558_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_a_3558_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3564_ = v_a_3558_;
v_isShared_3565_ = v_isSharedCheck_3573_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v_a_3558_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3573_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set_tag(v___x_3564_, 1);
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
lean_ctor_set(v___x_3568_, 1, v_snd_3540_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3568_);
v___x_3570_ = v___x_3560_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_object* v_a_3574_; 
lean_del_object(v___x_3560_);
lean_dec(v_snd_3540_);
v_a_3574_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v_a_3558_, 1);
v_a_3546_ = v_a_3574_;
goto v___jp_3545_;
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_del_object(v___x_3542_);
lean_dec(v_snd_3540_);
v_a_3576_ = lean_ctor_get(v___y_3557_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___y_3557_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___y_3557_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___y_3557_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2___boxed(lean_object* v_a_3604_, lean_object* v_as_3605_, lean_object* v_sz_3606_, lean_object* v_i_3607_, lean_object* v_b_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
size_t v_sz_boxed_3620_; size_t v_i_boxed_3621_; lean_object* v_res_3622_; 
v_sz_boxed_3620_ = lean_unbox_usize(v_sz_3606_);
lean_dec(v_sz_3606_);
v_i_boxed_3621_ = lean_unbox_usize(v_i_3607_);
lean_dec(v_i_3607_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3604_, v_as_3605_, v_sz_boxed_3620_, v_i_boxed_3621_, v_b_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v_as_3605_);
lean_dec_ref(v_a_3604_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(lean_object* v_a_3623_, lean_object* v_t_3624_, lean_object* v_init_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_root_3637_; lean_object* v_tail_3638_; lean_object* v___x_3639_; 
v_root_3637_ = lean_ctor_get(v_t_3624_, 0);
v_tail_3638_ = lean_ctor_get(v_t_3624_, 1);
lean_inc(v_init_3625_);
v___x_3639_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3625_, v_a_3623_, v_root_3637_, v_init_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v_init_3625_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3676_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3676_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3676_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
if (lean_obj_tag(v_a_3640_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; 
v_a_3644_ = lean_ctor_get(v_a_3640_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v_a_3640_, 1);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v_a_3644_);
v___x_3646_ = v___x_3642_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; size_t v_sz_3651_; size_t v___x_3652_; lean_object* v___x_3653_; 
lean_del_object(v___x_3642_);
v_a_3648_ = lean_ctor_get(v_a_3640_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v_a_3640_, 1);
v___x_3649_ = lean_box(0);
v___x_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
lean_ctor_set(v___x_3650_, 1, v_a_3648_);
v_sz_3651_ = lean_array_size(v_tail_3638_);
v___x_3652_ = ((size_t)0ULL);
v___x_3653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3623_, v_tail_3638_, v_sz_3651_, v___x_3652_, v___x_3650_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3667_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3656_ = v___x_3653_;
v_isShared_3657_ = v_isSharedCheck_3667_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3667_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v_fst_3658_; 
v_fst_3658_ = lean_ctor_get(v_a_3654_, 0);
if (lean_obj_tag(v_fst_3658_) == 0)
{
lean_object* v_snd_3659_; lean_object* v___x_3661_; 
v_snd_3659_ = lean_ctor_get(v_a_3654_, 1);
lean_inc(v_snd_3659_);
lean_dec(v_a_3654_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v_snd_3659_);
v___x_3661_ = v___x_3656_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_snd_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
else
{
lean_object* v_val_3663_; lean_object* v___x_3665_; 
lean_inc_ref(v_fst_3658_);
lean_dec(v_a_3654_);
v_val_3663_ = lean_ctor_get(v_fst_3658_, 0);
lean_inc(v_val_3663_);
lean_dec_ref_known(v_fst_3658_, 1);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v_val_3663_);
v___x_3665_ = v___x_3656_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_val_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
v_a_3668_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3653_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3653_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3639_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3639_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1___boxed(lean_object* v_a_3685_, lean_object* v_t_3686_, lean_object* v_init_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3685_, v_t_3686_, v_init_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v_t_3686_);
lean_dec_ref(v_a_3685_);
return v_res_3699_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3701_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0));
v___x_3702_ = lean_unsigned_to_nat(2u);
v___x_3703_ = lean_unsigned_to_nat(87u);
v___x_3704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3705_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3706_ = l_mkPanicMessageWithDecl(v___x_3705_, v___x_3704_, v___x_3703_, v___x_3702_, v___x_3701_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3707_, v_a_3715_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v_elimEqs_3720_; lean_object* v_vars_3721_; lean_object* v_size_3722_; lean_object* v_size_3723_; uint8_t v___x_3724_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v_elimEqs_3720_ = lean_ctor_get(v_a_3719_, 9);
lean_inc_ref(v_elimEqs_3720_);
v_vars_3721_ = lean_ctor_get(v_a_3719_, 0);
v_size_3722_ = lean_ctor_get(v_elimEqs_3720_, 2);
v_size_3723_ = lean_ctor_get(v_vars_3721_, 2);
v___x_3724_ = lean_nat_dec_eq(v_size_3722_, v_size_3723_);
if (v___x_3724_ == 0)
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec_ref(v_elimEqs_3720_);
lean_dec(v_a_3719_);
v___x_3725_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1);
v___x_3726_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_3725_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_);
return v___x_3726_;
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = lean_unsigned_to_nat(0u);
v___x_3728_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3719_, v_elimEqs_3720_, v___x_3727_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_);
lean_dec_ref(v_elimEqs_3720_);
lean_dec(v_a_3719_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3736_; 
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; 
v_unused_3737_ = lean_ctor_get(v___x_3728_, 0);
lean_dec(v_unused_3737_);
v___x_3730_ = v___x_3728_;
v_isShared_3731_ = v_isSharedCheck_3736_;
goto v_resetjp_3729_;
}
else
{
lean_dec(v___x_3728_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3736_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3732_; lean_object* v___x_3734_; 
v___x_3732_ = lean_box(0);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 0, v___x_3732_);
v___x_3734_ = v___x_3730_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
v_a_3738_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3728_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3728_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
v_a_3746_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3718_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3718_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___boxed(lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_a_3755_);
lean_dec(v_a_3754_);
return v_res_3765_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3768_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1));
v___x_3769_ = lean_unsigned_to_nat(4u);
v___x_3770_ = lean_unsigned_to_nat(99u);
v___x_3771_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0));
v___x_3772_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3773_ = l_mkPanicMessageWithDecl(v___x_3772_, v___x_3771_, v___x_3770_, v___x_3769_, v___x_3768_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(lean_object* v_as_x27_3774_, lean_object* v_b_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
if (lean_obj_tag(v_as_x27_3774_) == 0)
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3787_, 0, v_b_3775_);
return v___x_3787_;
}
else
{
lean_object* v_head_3788_; lean_object* v_tail_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_head_3788_ = lean_ctor_get(v_as_x27_3774_, 0);
v_tail_3789_ = lean_ctor_get(v_as_x27_3774_, 1);
v___x_3790_ = lean_box(0);
v___x_3791_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_head_3788_, v___y_3776_, v___y_3784_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; uint8_t v___x_3793_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = lean_unbox(v_a_3792_);
lean_dec(v_a_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2);
v___x_3795_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_3794_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3806_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3806_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3806_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
if (lean_obj_tag(v_a_3796_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; 
v_a_3800_ = lean_ctor_get(v_a_3796_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v_a_3796_, 1);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v_a_3800_);
v___x_3802_ = v___x_3798_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
else
{
lean_object* v_a_3804_; 
lean_del_object(v___x_3798_);
v_a_3804_ = lean_ctor_get(v_a_3796_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v_a_3796_, 1);
v_as_x27_3774_ = v_tail_3789_;
v_b_3775_ = v_a_3804_;
goto _start;
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
v_a_3807_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3795_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3795_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
v_as_x27_3774_ = v_tail_3789_;
v_b_3775_ = v___x_3790_;
goto _start;
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
v_a_3816_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3791_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3791_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___boxed(lean_object* v_as_x27_3824_, lean_object* v_b_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3824_, v_b_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec(v_as_x27_3824_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3838_, v_a_3846_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v_elimStack_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v_elimStack_3851_ = lean_ctor_get(v_a_3850_, 10);
lean_inc(v_elimStack_3851_);
lean_dec(v_a_3850_);
v___x_3852_ = lean_box(0);
v___x_3853_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_elimStack_3851_, v___x_3852_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
lean_dec(v_elimStack_3851_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3860_ == 0)
{
lean_object* v_unused_3861_; 
v_unused_3861_ = lean_ctor_get(v___x_3853_, 0);
lean_dec(v_unused_3861_);
v___x_3855_ = v___x_3853_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_dec(v___x_3853_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3852_);
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3852_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
else
{
return v___x_3853_;
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
v_a_3862_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3849_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3849_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack___boxed(lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec(v_a_3870_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(lean_object* v_as_3882_, lean_object* v_as_x27_3883_, lean_object* v_b_3884_, lean_object* v_a_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3883_, v_b_3884_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___boxed(lean_object* v_as_3898_, lean_object* v_as_x27_3899_, lean_object* v_b_3900_, lean_object* v_a_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(v_as_3898_, v_as_x27_3899_, v_b_3900_, v_a_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec(v_as_x27_3899_);
lean_dec(v_as_3898_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_3917_, lean_object* v_as_3918_, size_t v_sz_3919_, size_t v_i_3920_, lean_object* v_b_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
uint8_t v___x_3933_; 
v___x_3933_ = lean_usize_dec_lt(v_i_3920_, v_sz_3919_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_b_3921_);
return v___x_3934_;
}
else
{
lean_object* v_a_3935_; lean_object* v_p_3936_; lean_object* v___x_3937_; 
lean_dec_ref(v_b_3921_);
v_a_3935_ = lean_array_uget_borrowed(v_as_3918_, v_i_3920_);
v_p_3936_ = lean_ctor_get(v_a_3935_, 0);
v___x_3937_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_3936_, v_____s_3917_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v___x_3938_; size_t v___x_3939_; size_t v___x_3940_; 
lean_dec_ref_known(v___x_3937_, 1);
v___x_3938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_3939_ = ((size_t)1ULL);
v___x_3940_ = lean_usize_add(v_i_3920_, v___x_3939_);
v_i_3920_ = v___x_3940_;
v_b_3921_ = v___x_3938_;
goto _start;
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
v_a_3942_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3937_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3937_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object* v_____s_3950_, lean_object* v_as_3951_, lean_object* v_sz_3952_, lean_object* v_i_3953_, lean_object* v_b_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
size_t v_sz_boxed_3966_; size_t v_i_boxed_3967_; lean_object* v_res_3968_; 
v_sz_boxed_3966_ = lean_unbox_usize(v_sz_3952_);
lean_dec(v_sz_3952_);
v_i_boxed_3967_ = lean_unbox_usize(v_i_3953_);
lean_dec(v_i_3953_);
v_res_3968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3950_, v_as_3951_, v_sz_boxed_3966_, v_i_boxed_3967_, v_b_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v_as_3951_);
lean_dec(v_____s_3950_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_3969_, lean_object* v_as_3970_, size_t v_sz_3971_, size_t v_i_3972_, lean_object* v_b_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
uint8_t v___x_3985_; 
v___x_3985_ = lean_usize_dec_lt(v_i_3972_, v_sz_3971_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; 
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v_b_3973_);
return v___x_3986_;
}
else
{
lean_object* v_a_3987_; lean_object* v_p_3988_; lean_object* v___x_3989_; 
lean_dec_ref(v_b_3973_);
v_a_3987_ = lean_array_uget_borrowed(v_as_3970_, v_i_3972_);
v_p_3988_ = lean_ctor_get(v_a_3987_, 0);
v___x_3989_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_3988_, v_____s_3969_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v___x_3990_; size_t v___x_3991_; size_t v___x_3992_; lean_object* v___x_3993_; 
lean_dec_ref_known(v___x_3989_, 1);
v___x_3990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_3991_ = ((size_t)1ULL);
v___x_3992_ = lean_usize_add(v_i_3972_, v___x_3991_);
v___x_3993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3969_, v_as_3970_, v_sz_3971_, v___x_3992_, v___x_3990_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
return v___x_3993_;
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
v_a_3994_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3989_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3989_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object* v_____s_4002_, lean_object* v_as_4003_, lean_object* v_sz_4004_, lean_object* v_i_4005_, lean_object* v_b_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
size_t v_sz_boxed_4018_; size_t v_i_boxed_4019_; lean_object* v_res_4020_; 
v_sz_boxed_4018_ = lean_unbox_usize(v_sz_4004_);
lean_dec(v_sz_4004_);
v_i_boxed_4019_ = lean_unbox_usize(v_i_4005_);
lean_dec(v_i_4005_);
v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4002_, v_as_4003_, v_sz_boxed_4018_, v_i_boxed_4019_, v_b_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v_as_4003_);
lean_dec(v_____s_4002_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_4024_, lean_object* v_as_4025_, size_t v_sz_4026_, size_t v_i_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
uint8_t v___x_4040_; 
v___x_4040_ = lean_usize_dec_lt(v_i_4027_, v_sz_4026_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v_b_4028_);
return v___x_4041_;
}
else
{
lean_object* v_a_4042_; lean_object* v_p_4043_; lean_object* v___x_4044_; 
lean_dec_ref(v_b_4028_);
v_a_4042_ = lean_array_uget_borrowed(v_as_4025_, v_i_4027_);
v_p_4043_ = lean_ctor_get(v_a_4042_, 0);
v___x_4044_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4043_, v_____s_4024_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v___x_4045_; size_t v___x_4046_; size_t v___x_4047_; 
lean_dec_ref_known(v___x_4044_, 1);
v___x_4045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4046_ = ((size_t)1ULL);
v___x_4047_ = lean_usize_add(v_i_4027_, v___x_4046_);
v_i_4027_ = v___x_4047_;
v_b_4028_ = v___x_4045_;
goto _start;
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
v_a_4049_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4044_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4044_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_____s_4057_, lean_object* v_as_4058_, lean_object* v_sz_4059_, lean_object* v_i_4060_, lean_object* v_b_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
size_t v_sz_boxed_4073_; size_t v_i_boxed_4074_; lean_object* v_res_4075_; 
v_sz_boxed_4073_ = lean_unbox_usize(v_sz_4059_);
lean_dec(v_sz_4059_);
v_i_boxed_4074_ = lean_unbox_usize(v_i_4060_);
lean_dec(v_i_4060_);
v_res_4075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4057_, v_as_4058_, v_sz_boxed_4073_, v_i_boxed_4074_, v_b_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v_as_4058_);
lean_dec(v_____s_4057_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_4076_, lean_object* v_as_4077_, size_t v_sz_4078_, size_t v_i_4079_, lean_object* v_b_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
uint8_t v___x_4092_; 
v___x_4092_ = lean_usize_dec_lt(v_i_4079_, v_sz_4078_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v_b_4080_);
return v___x_4093_;
}
else
{
lean_object* v_a_4094_; lean_object* v_p_4095_; lean_object* v___x_4096_; 
lean_dec_ref(v_b_4080_);
v_a_4094_ = lean_array_uget_borrowed(v_as_4077_, v_i_4079_);
v_p_4095_ = lean_ctor_get(v_a_4094_, 0);
v___x_4096_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4095_, v_____s_4076_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v___x_4097_; size_t v___x_4098_; size_t v___x_4099_; lean_object* v___x_4100_; 
lean_dec_ref_known(v___x_4096_, 1);
v___x_4097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4098_ = ((size_t)1ULL);
v___x_4099_ = lean_usize_add(v_i_4079_, v___x_4098_);
v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4076_, v_as_4077_, v_sz_4078_, v___x_4099_, v___x_4097_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
return v___x_4100_;
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_a_4101_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4096_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4096_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_____s_4109_, lean_object* v_as_4110_, lean_object* v_sz_4111_, lean_object* v_i_4112_, lean_object* v_b_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
size_t v_sz_boxed_4125_; size_t v_i_boxed_4126_; lean_object* v_res_4127_; 
v_sz_boxed_4125_ = lean_unbox_usize(v_sz_4111_);
lean_dec(v_sz_4111_);
v_i_boxed_4126_ = lean_unbox_usize(v_i_4112_);
lean_dec(v_i_4112_);
v_res_4127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4109_, v_as_4110_, v_sz_boxed_4125_, v_i_boxed_4126_, v_b_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v_as_4110_);
lean_dec(v_____s_4109_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_init_4128_, lean_object* v_____s_4129_, lean_object* v_n_4130_, lean_object* v_b_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
if (lean_obj_tag(v_n_4130_) == 0)
{
lean_object* v_cs_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; size_t v_sz_4146_; size_t v___x_4147_; lean_object* v___x_4148_; 
v_cs_4143_ = lean_ctor_get(v_n_4130_, 0);
v___x_4144_ = lean_box(0);
v___x_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
lean_ctor_set(v___x_4145_, 1, v_b_4131_);
v_sz_4146_ = lean_array_size(v_cs_4143_);
v___x_4147_ = ((size_t)0ULL);
v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4128_, v_____s_4129_, v_cs_4143_, v_sz_4146_, v___x_4147_, v___x_4145_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4163_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4163_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4163_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v_fst_4153_; 
v_fst_4153_ = lean_ctor_get(v_a_4149_, 0);
if (lean_obj_tag(v_fst_4153_) == 0)
{
lean_object* v_snd_4154_; lean_object* v___x_4155_; lean_object* v___x_4157_; 
v_snd_4154_ = lean_ctor_get(v_a_4149_, 1);
lean_inc(v_snd_4154_);
lean_dec(v_a_4149_);
v___x_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_snd_4154_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4155_);
v___x_4157_ = v___x_4151_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
else
{
lean_object* v_val_4159_; lean_object* v___x_4161_; 
lean_inc_ref(v_fst_4153_);
lean_dec(v_a_4149_);
v_val_4159_ = lean_ctor_get(v_fst_4153_, 0);
lean_inc(v_val_4159_);
lean_dec_ref_known(v_fst_4153_, 1);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v_val_4159_);
v___x_4161_ = v___x_4151_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_val_4159_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
v_a_4164_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4148_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4148_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
else
{
lean_object* v_vs_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; size_t v_sz_4175_; size_t v___x_4176_; lean_object* v___x_4177_; 
v_vs_4172_ = lean_ctor_get(v_n_4130_, 0);
v___x_4173_ = lean_box(0);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
lean_ctor_set(v___x_4174_, 1, v_b_4131_);
v_sz_4175_ = lean_array_size(v_vs_4172_);
v___x_4176_ = ((size_t)0ULL);
v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4129_, v_vs_4172_, v_sz_4175_, v___x_4176_, v___x_4174_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4192_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4180_ = v___x_4177_;
v_isShared_4181_ = v_isSharedCheck_4192_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4192_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v_fst_4182_; 
v_fst_4182_ = lean_ctor_get(v_a_4178_, 0);
if (lean_obj_tag(v_fst_4182_) == 0)
{
lean_object* v_snd_4183_; lean_object* v___x_4184_; lean_object* v___x_4186_; 
v_snd_4183_ = lean_ctor_get(v_a_4178_, 1);
lean_inc(v_snd_4183_);
lean_dec(v_a_4178_);
v___x_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4184_, 0, v_snd_4183_);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v___x_4184_);
v___x_4186_ = v___x_4180_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
else
{
lean_object* v_val_4188_; lean_object* v___x_4190_; 
lean_inc_ref(v_fst_4182_);
lean_dec(v_a_4178_);
v_val_4188_ = lean_ctor_get(v_fst_4182_, 0);
lean_inc(v_val_4188_);
lean_dec_ref_known(v_fst_4182_, 1);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v_val_4188_);
v___x_4190_ = v___x_4180_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_val_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
v_a_4193_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4177_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4177_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_4201_, lean_object* v_____s_4202_, lean_object* v_as_4203_, size_t v_sz_4204_, size_t v_i_4205_, lean_object* v_b_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
uint8_t v___x_4218_; 
v___x_4218_ = lean_usize_dec_lt(v_i_4205_, v_sz_4204_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; 
v___x_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4219_, 0, v_b_4206_);
return v___x_4219_;
}
else
{
lean_object* v_snd_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4254_; 
v_snd_4220_ = lean_ctor_get(v_b_4206_, 1);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_b_4206_);
if (v_isSharedCheck_4254_ == 0)
{
lean_object* v_unused_4255_; 
v_unused_4255_ = lean_ctor_get(v_b_4206_, 0);
lean_dec(v_unused_4255_);
v___x_4222_ = v_b_4206_;
v_isShared_4223_ = v_isSharedCheck_4254_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_snd_4220_);
lean_dec(v_b_4206_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4254_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4224_; lean_object* v_a_4225_; lean_object* v___x_4226_; 
v___x_4224_ = lean_box(0);
v_a_4225_ = lean_array_uget_borrowed(v_as_4203_, v_i_4205_);
lean_inc(v_snd_4220_);
v___x_4226_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4201_, v_____s_4202_, v_a_4225_, v_snd_4220_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4245_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4229_ = v___x_4226_;
v_isShared_4230_ = v_isSharedCheck_4245_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4245_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
if (lean_obj_tag(v_a_4227_) == 0)
{
lean_object* v___x_4231_; lean_object* v___x_4233_; 
v___x_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4231_, 0, v_a_4227_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4231_);
v___x_4233_ = v___x_4222_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4231_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_snd_4220_);
v___x_4233_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4235_; 
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4233_);
v___x_4235_ = v___x_4229_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; 
lean_del_object(v___x_4229_);
lean_dec(v_snd_4220_);
v_a_4238_ = lean_ctor_get(v_a_4227_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v_a_4227_, 1);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 1, v_a_4238_);
lean_ctor_set(v___x_4222_, 0, v___x_4224_);
v___x_4240_ = v___x_4222_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_a_4238_);
v___x_4240_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
size_t v___x_4241_; size_t v___x_4242_; 
v___x_4241_ = ((size_t)1ULL);
v___x_4242_ = lean_usize_add(v_i_4205_, v___x_4241_);
v_i_4205_ = v___x_4242_;
v_b_4206_ = v___x_4240_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_del_object(v___x_4222_);
lean_dec(v_snd_4220_);
v_a_4246_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4226_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4226_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_4256_ = _args[0];
lean_object* v_____s_4257_ = _args[1];
lean_object* v_as_4258_ = _args[2];
lean_object* v_sz_4259_ = _args[3];
lean_object* v_i_4260_ = _args[4];
lean_object* v_b_4261_ = _args[5];
lean_object* v___y_4262_ = _args[6];
lean_object* v___y_4263_ = _args[7];
lean_object* v___y_4264_ = _args[8];
lean_object* v___y_4265_ = _args[9];
lean_object* v___y_4266_ = _args[10];
lean_object* v___y_4267_ = _args[11];
lean_object* v___y_4268_ = _args[12];
lean_object* v___y_4269_ = _args[13];
lean_object* v___y_4270_ = _args[14];
lean_object* v___y_4271_ = _args[15];
lean_object* v___y_4272_ = _args[16];
_start:
{
size_t v_sz_boxed_4273_; size_t v_i_boxed_4274_; lean_object* v_res_4275_; 
v_sz_boxed_4273_ = lean_unbox_usize(v_sz_4259_);
lean_dec(v_sz_4259_);
v_i_boxed_4274_ = lean_unbox_usize(v_i_4260_);
lean_dec(v_i_4260_);
v_res_4275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4256_, v_____s_4257_, v_as_4258_, v_sz_boxed_4273_, v_i_boxed_4274_, v_b_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v_as_4258_);
lean_dec(v_____s_4257_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_init_4276_, lean_object* v_____s_4277_, lean_object* v_n_4278_, lean_object* v_b_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4276_, v_____s_4277_, v_n_4278_, v_b_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
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
lean_dec_ref(v_n_4278_);
lean_dec(v_____s_4277_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(lean_object* v_____s_4292_, lean_object* v_t_4293_, lean_object* v_init_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_root_4306_; lean_object* v_tail_4307_; lean_object* v___x_4308_; 
v_root_4306_ = lean_ctor_get(v_t_4293_, 0);
v_tail_4307_ = lean_ctor_get(v_t_4293_, 1);
v___x_4308_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4294_, v_____s_4292_, v_root_4306_, v_init_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4345_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4311_ = v___x_4308_;
v_isShared_4312_ = v_isSharedCheck_4345_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4308_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4345_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
if (lean_obj_tag(v_a_4309_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4315_; 
v_a_4313_ = lean_ctor_get(v_a_4309_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v_a_4309_, 1);
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 0, v_a_4313_);
v___x_4315_ = v___x_4311_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4313_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; size_t v_sz_4320_; size_t v___x_4321_; lean_object* v___x_4322_; 
lean_del_object(v___x_4311_);
v_a_4317_ = lean_ctor_get(v_a_4309_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v_a_4309_, 1);
v___x_4318_ = lean_box(0);
v___x_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
lean_ctor_set(v___x_4319_, 1, v_a_4317_);
v_sz_4320_ = lean_array_size(v_tail_4307_);
v___x_4321_ = ((size_t)0ULL);
v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4292_, v_tail_4307_, v_sz_4320_, v___x_4321_, v___x_4319_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4336_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4336_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4336_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v_fst_4327_; 
v_fst_4327_ = lean_ctor_get(v_a_4323_, 0);
if (lean_obj_tag(v_fst_4327_) == 0)
{
lean_object* v_snd_4328_; lean_object* v___x_4330_; 
v_snd_4328_ = lean_ctor_get(v_a_4323_, 1);
lean_inc(v_snd_4328_);
lean_dec(v_a_4323_);
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 0, v_snd_4328_);
v___x_4330_ = v___x_4325_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_snd_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
else
{
lean_object* v_val_4332_; lean_object* v___x_4334_; 
lean_inc_ref(v_fst_4327_);
lean_dec(v_a_4323_);
v_val_4332_ = lean_ctor_get(v_fst_4327_, 0);
lean_inc(v_val_4332_);
lean_dec_ref_known(v_fst_4327_, 1);
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 0, v_val_4332_);
v___x_4334_ = v___x_4325_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_val_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
v_a_4337_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4322_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4322_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
v_a_4346_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4308_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4308_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_4354_, lean_object* v_t_4355_, lean_object* v_init_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_____s_4354_, v_t_4355_, v_init_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v_t_4355_);
lean_dec(v_____s_4354_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_4369_, size_t v_sz_4370_, size_t v_i_4371_, lean_object* v_b_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
uint8_t v___x_4384_; 
v___x_4384_ = lean_usize_dec_lt(v_i_4371_, v_sz_4370_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; 
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v_b_4372_);
return v___x_4385_;
}
else
{
lean_object* v_snd_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4410_; 
v_snd_4386_ = lean_ctor_get(v_b_4372_, 1);
v_isSharedCheck_4410_ = !lean_is_exclusive(v_b_4372_);
if (v_isSharedCheck_4410_ == 0)
{
lean_object* v_unused_4411_; 
v_unused_4411_ = lean_ctor_get(v_b_4372_, 0);
lean_dec(v_unused_4411_);
v___x_4388_ = v_b_4372_;
v_isShared_4389_ = v_isSharedCheck_4410_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_snd_4386_);
lean_dec(v_b_4372_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4410_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4390_; lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4390_ = lean_box(0);
v_a_4391_ = lean_array_uget_borrowed(v_as_4369_, v_i_4371_);
v___x_4392_ = lean_box(0);
v___x_4393_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4386_, v_a_4391_, v___x_4392_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4397_; 
lean_dec_ref_known(v___x_4393_, 1);
v___x_4394_ = lean_unsigned_to_nat(1u);
v___x_4395_ = lean_nat_add(v_snd_4386_, v___x_4394_);
lean_dec(v_snd_4386_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 1, v___x_4395_);
lean_ctor_set(v___x_4388_, 0, v___x_4390_);
v___x_4397_ = v___x_4388_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4390_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v___x_4395_);
v___x_4397_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
size_t v___x_4398_; size_t v___x_4399_; 
v___x_4398_ = ((size_t)1ULL);
v___x_4399_ = lean_usize_add(v_i_4371_, v___x_4398_);
v_i_4371_ = v___x_4399_;
v_b_4372_ = v___x_4397_;
goto _start;
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_del_object(v___x_4388_);
lean_dec(v_snd_4386_);
v_a_4402_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4393_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4393_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_4412_, lean_object* v_sz_4413_, lean_object* v_i_4414_, lean_object* v_b_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
size_t v_sz_boxed_4427_; size_t v_i_boxed_4428_; lean_object* v_res_4429_; 
v_sz_boxed_4427_ = lean_unbox_usize(v_sz_4413_);
lean_dec(v_sz_4413_);
v_i_boxed_4428_ = lean_unbox_usize(v_i_4414_);
lean_dec(v_i_4414_);
v_res_4429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4412_, v_sz_boxed_4427_, v_i_boxed_4428_, v_b_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v_as_4412_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_4430_, size_t v_sz_4431_, size_t v_i_4432_, lean_object* v_b_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
uint8_t v___x_4445_; 
v___x_4445_ = lean_usize_dec_lt(v_i_4432_, v_sz_4431_);
if (v___x_4445_ == 0)
{
lean_object* v___x_4446_; 
v___x_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4446_, 0, v_b_4433_);
return v___x_4446_;
}
else
{
lean_object* v_snd_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4471_; 
v_snd_4447_ = lean_ctor_get(v_b_4433_, 1);
v_isSharedCheck_4471_ = !lean_is_exclusive(v_b_4433_);
if (v_isSharedCheck_4471_ == 0)
{
lean_object* v_unused_4472_; 
v_unused_4472_ = lean_ctor_get(v_b_4433_, 0);
lean_dec(v_unused_4472_);
v___x_4449_ = v_b_4433_;
v_isShared_4450_ = v_isSharedCheck_4471_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_snd_4447_);
lean_dec(v_b_4433_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4471_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4451_; lean_object* v_a_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4451_ = lean_box(0);
v_a_4452_ = lean_array_uget_borrowed(v_as_4430_, v_i_4432_);
v___x_4453_ = lean_box(0);
v___x_4454_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4447_, v_a_4452_, v___x_4453_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4458_; 
lean_dec_ref_known(v___x_4454_, 1);
v___x_4455_ = lean_unsigned_to_nat(1u);
v___x_4456_ = lean_nat_add(v_snd_4447_, v___x_4455_);
lean_dec(v_snd_4447_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 1, v___x_4456_);
lean_ctor_set(v___x_4449_, 0, v___x_4451_);
v___x_4458_ = v___x_4449_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4451_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
size_t v___x_4459_; size_t v___x_4460_; lean_object* v___x_4461_; 
v___x_4459_ = ((size_t)1ULL);
v___x_4460_ = lean_usize_add(v_i_4432_, v___x_4459_);
v___x_4461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4430_, v_sz_4431_, v___x_4460_, v___x_4458_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
return v___x_4461_;
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_del_object(v___x_4449_);
lean_dec(v_snd_4447_);
v_a_4463_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4454_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4454_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_4473_, lean_object* v_sz_4474_, lean_object* v_i_4475_, lean_object* v_b_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
size_t v_sz_boxed_4488_; size_t v_i_boxed_4489_; lean_object* v_res_4490_; 
v_sz_boxed_4488_ = lean_unbox_usize(v_sz_4474_);
lean_dec(v_sz_4474_);
v_i_boxed_4489_ = lean_unbox_usize(v_i_4475_);
lean_dec(v_i_4475_);
v_res_4490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_4473_, v_sz_boxed_4488_, v_i_boxed_4489_, v_b_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v_as_4473_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_init_4491_, lean_object* v_n_4492_, lean_object* v_b_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
if (lean_obj_tag(v_n_4492_) == 0)
{
lean_object* v_cs_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; size_t v_sz_4508_; size_t v___x_4509_; lean_object* v___x_4510_; 
v_cs_4505_ = lean_ctor_get(v_n_4492_, 0);
v___x_4506_ = lean_box(0);
v___x_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
lean_ctor_set(v___x_4507_, 1, v_b_4493_);
v_sz_4508_ = lean_array_size(v_cs_4505_);
v___x_4509_ = ((size_t)0ULL);
v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4491_, v_cs_4505_, v_sz_4508_, v___x_4509_, v___x_4507_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4525_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4513_ = v___x_4510_;
v_isShared_4514_ = v_isSharedCheck_4525_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4510_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4525_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v_fst_4515_; 
v_fst_4515_ = lean_ctor_get(v_a_4511_, 0);
if (lean_obj_tag(v_fst_4515_) == 0)
{
lean_object* v_snd_4516_; lean_object* v___x_4517_; lean_object* v___x_4519_; 
v_snd_4516_ = lean_ctor_get(v_a_4511_, 1);
lean_inc(v_snd_4516_);
lean_dec(v_a_4511_);
v___x_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4517_, 0, v_snd_4516_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___x_4517_);
v___x_4519_ = v___x_4513_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4517_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
else
{
lean_object* v_val_4521_; lean_object* v___x_4523_; 
lean_inc_ref(v_fst_4515_);
lean_dec(v_a_4511_);
v_val_4521_ = lean_ctor_get(v_fst_4515_, 0);
lean_inc(v_val_4521_);
lean_dec_ref_known(v_fst_4515_, 1);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v_val_4521_);
v___x_4523_ = v___x_4513_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_val_4521_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
v_a_4526_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4510_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4510_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
else
{
lean_object* v_vs_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; size_t v_sz_4537_; size_t v___x_4538_; lean_object* v___x_4539_; 
v_vs_4534_ = lean_ctor_get(v_n_4492_, 0);
v___x_4535_ = lean_box(0);
v___x_4536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
lean_ctor_set(v___x_4536_, 1, v_b_4493_);
v_sz_4537_ = lean_array_size(v_vs_4534_);
v___x_4538_ = ((size_t)0ULL);
v___x_4539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_4534_, v_sz_4537_, v___x_4538_, v___x_4536_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4554_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4542_ = v___x_4539_;
v_isShared_4543_ = v_isSharedCheck_4554_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4539_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4554_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v_fst_4544_; 
v_fst_4544_ = lean_ctor_get(v_a_4540_, 0);
if (lean_obj_tag(v_fst_4544_) == 0)
{
lean_object* v_snd_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
v_snd_4545_ = lean_ctor_get(v_a_4540_, 1);
lean_inc(v_snd_4545_);
lean_dec(v_a_4540_);
v___x_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4546_, 0, v_snd_4545_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v___x_4546_);
v___x_4548_ = v___x_4542_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
else
{
lean_object* v_val_4550_; lean_object* v___x_4552_; 
lean_inc_ref(v_fst_4544_);
lean_dec(v_a_4540_);
v_val_4550_ = lean_ctor_get(v_fst_4544_, 0);
lean_inc(v_val_4550_);
lean_dec_ref_known(v_fst_4544_, 1);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v_val_4550_);
v___x_4552_ = v___x_4542_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_val_4550_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
v_a_4555_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4539_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4539_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_init_4563_, lean_object* v_as_4564_, size_t v_sz_4565_, size_t v_i_4566_, lean_object* v_b_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
uint8_t v___x_4579_; 
v___x_4579_ = lean_usize_dec_lt(v_i_4566_, v_sz_4565_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v_b_4567_);
return v___x_4580_;
}
else
{
lean_object* v_snd_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4615_; 
v_snd_4581_ = lean_ctor_get(v_b_4567_, 1);
v_isSharedCheck_4615_ = !lean_is_exclusive(v_b_4567_);
if (v_isSharedCheck_4615_ == 0)
{
lean_object* v_unused_4616_; 
v_unused_4616_ = lean_ctor_get(v_b_4567_, 0);
lean_dec(v_unused_4616_);
v___x_4583_ = v_b_4567_;
v_isShared_4584_ = v_isSharedCheck_4615_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_snd_4581_);
lean_dec(v_b_4567_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4615_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v_a_4586_; lean_object* v___x_4587_; 
v___x_4585_ = lean_box(0);
v_a_4586_ = lean_array_uget_borrowed(v_as_4564_, v_i_4566_);
lean_inc(v_snd_4581_);
v___x_4587_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4563_, v_a_4586_, v_snd_4581_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4606_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4590_ = v___x_4587_;
v_isShared_4591_ = v_isSharedCheck_4606_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4587_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4606_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
if (lean_obj_tag(v_a_4588_) == 0)
{
lean_object* v___x_4592_; lean_object* v___x_4594_; 
v___x_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4592_, 0, v_a_4588_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4592_);
v___x_4594_ = v___x_4583_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4592_);
lean_ctor_set(v_reuseFailAlloc_4598_, 1, v_snd_4581_);
v___x_4594_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4596_; 
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
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; 
lean_del_object(v___x_4590_);
lean_dec(v_snd_4581_);
v_a_4599_ = lean_ctor_get(v_a_4588_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v_a_4588_, 1);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 1, v_a_4599_);
lean_ctor_set(v___x_4583_, 0, v___x_4585_);
v___x_4601_ = v___x_4583_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4585_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_a_4599_);
v___x_4601_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
size_t v___x_4602_; size_t v___x_4603_; 
v___x_4602_ = ((size_t)1ULL);
v___x_4603_ = lean_usize_add(v_i_4566_, v___x_4602_);
v_i_4566_ = v___x_4603_;
v_b_4567_ = v___x_4601_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_del_object(v___x_4583_);
lean_dec(v_snd_4581_);
v_a_4607_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4587_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4587_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object* v_init_4617_, lean_object* v_as_4618_, lean_object* v_sz_4619_, lean_object* v_i_4620_, lean_object* v_b_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
size_t v_sz_boxed_4633_; size_t v_i_boxed_4634_; lean_object* v_res_4635_; 
v_sz_boxed_4633_ = lean_unbox_usize(v_sz_4619_);
lean_dec(v_sz_4619_);
v_i_boxed_4634_ = lean_unbox_usize(v_i_4620_);
lean_dec(v_i_4620_);
v_res_4635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4617_, v_as_4618_, v_sz_boxed_4633_, v_i_boxed_4634_, v_b_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v_as_4618_);
lean_dec(v_init_4617_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_init_4636_, lean_object* v_n_4637_, lean_object* v_b_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4636_, v_n_4637_, v_b_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v_n_4637_);
lean_dec(v_init_4636_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_4651_, size_t v_sz_4652_, size_t v_i_4653_, lean_object* v_b_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
uint8_t v___x_4666_; 
v___x_4666_ = lean_usize_dec_lt(v_i_4653_, v_sz_4652_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; 
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v_b_4654_);
return v___x_4667_;
}
else
{
lean_object* v_snd_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4692_; 
v_snd_4668_ = lean_ctor_get(v_b_4654_, 1);
v_isSharedCheck_4692_ = !lean_is_exclusive(v_b_4654_);
if (v_isSharedCheck_4692_ == 0)
{
lean_object* v_unused_4693_; 
v_unused_4693_ = lean_ctor_get(v_b_4654_, 0);
lean_dec(v_unused_4693_);
v___x_4670_ = v_b_4654_;
v_isShared_4671_ = v_isSharedCheck_4692_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_snd_4668_);
lean_dec(v_b_4654_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4692_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4672_; lean_object* v_a_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4672_ = lean_box(0);
v_a_4673_ = lean_array_uget_borrowed(v_as_4651_, v_i_4653_);
v___x_4674_ = lean_box(0);
v___x_4675_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4668_, v_a_4673_, v___x_4674_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
lean_dec_ref_known(v___x_4675_, 1);
v___x_4676_ = lean_unsigned_to_nat(1u);
v___x_4677_ = lean_nat_add(v_snd_4668_, v___x_4676_);
lean_dec(v_snd_4668_);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 1, v___x_4677_);
lean_ctor_set(v___x_4670_, 0, v___x_4672_);
v___x_4679_ = v___x_4670_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4672_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v___x_4677_);
v___x_4679_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
size_t v___x_4680_; size_t v___x_4681_; 
v___x_4680_ = ((size_t)1ULL);
v___x_4681_ = lean_usize_add(v_i_4653_, v___x_4680_);
v_i_4653_ = v___x_4681_;
v_b_4654_ = v___x_4679_;
goto _start;
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_del_object(v___x_4670_);
lean_dec(v_snd_4668_);
v_a_4684_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4675_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4675_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_4694_, lean_object* v_sz_4695_, lean_object* v_i_4696_, lean_object* v_b_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
size_t v_sz_boxed_4709_; size_t v_i_boxed_4710_; lean_object* v_res_4711_; 
v_sz_boxed_4709_ = lean_unbox_usize(v_sz_4695_);
lean_dec(v_sz_4695_);
v_i_boxed_4710_ = lean_unbox_usize(v_i_4696_);
lean_dec(v_i_4696_);
v_res_4711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4694_, v_sz_boxed_4709_, v_i_boxed_4710_, v_b_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v_as_4694_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_4712_, size_t v_sz_4713_, size_t v_i_4714_, lean_object* v_b_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
uint8_t v___x_4727_; 
v___x_4727_ = lean_usize_dec_lt(v_i_4714_, v_sz_4713_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; 
v___x_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4728_, 0, v_b_4715_);
return v___x_4728_;
}
else
{
lean_object* v_snd_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4753_; 
v_snd_4729_ = lean_ctor_get(v_b_4715_, 1);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_b_4715_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v_b_4715_, 0);
lean_dec(v_unused_4754_);
v___x_4731_ = v_b_4715_;
v_isShared_4732_ = v_isSharedCheck_4753_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_snd_4729_);
lean_dec(v_b_4715_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4753_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4733_; lean_object* v_a_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4733_ = lean_box(0);
v_a_4734_ = lean_array_uget_borrowed(v_as_4712_, v_i_4714_);
v___x_4735_ = lean_box(0);
v___x_4736_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4729_, v_a_4734_, v___x_4735_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4740_; 
lean_dec_ref_known(v___x_4736_, 1);
v___x_4737_ = lean_unsigned_to_nat(1u);
v___x_4738_ = lean_nat_add(v_snd_4729_, v___x_4737_);
lean_dec(v_snd_4729_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 1, v___x_4738_);
lean_ctor_set(v___x_4731_, 0, v___x_4733_);
v___x_4740_ = v___x_4731_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v___x_4738_);
v___x_4740_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
size_t v___x_4741_; size_t v___x_4742_; lean_object* v___x_4743_; 
v___x_4741_ = ((size_t)1ULL);
v___x_4742_ = lean_usize_add(v_i_4714_, v___x_4741_);
v___x_4743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4712_, v_sz_4713_, v___x_4742_, v___x_4740_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
return v___x_4743_;
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
lean_del_object(v___x_4731_);
lean_dec(v_snd_4729_);
v_a_4745_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4736_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4736_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_4755_, lean_object* v_sz_4756_, lean_object* v_i_4757_, lean_object* v_b_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
size_t v_sz_boxed_4770_; size_t v_i_boxed_4771_; lean_object* v_res_4772_; 
v_sz_boxed_4770_ = lean_unbox_usize(v_sz_4756_);
lean_dec(v_sz_4756_);
v_i_boxed_4771_ = lean_unbox_usize(v_i_4757_);
lean_dec(v_i_4757_);
v_res_4772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_as_4755_, v_sz_boxed_4770_, v_i_boxed_4771_, v_b_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v_as_4755_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(lean_object* v_t_4773_, lean_object* v_init_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v_root_4786_; lean_object* v_tail_4787_; lean_object* v___x_4788_; 
v_root_4786_ = lean_ctor_get(v_t_4773_, 0);
v_tail_4787_ = lean_ctor_get(v_t_4773_, 1);
lean_inc(v_init_4774_);
v___x_4788_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4774_, v_root_4786_, v_init_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
lean_dec(v_init_4774_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4825_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4791_ = v___x_4788_;
v_isShared_4792_ = v_isSharedCheck_4825_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4825_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
if (lean_obj_tag(v_a_4789_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4795_; 
v_a_4793_ = lean_ctor_get(v_a_4789_, 0);
lean_inc(v_a_4793_);
lean_dec_ref_known(v_a_4789_, 1);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v_a_4793_);
v___x_4795_ = v___x_4791_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4793_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
else
{
lean_object* v_a_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; size_t v_sz_4800_; size_t v___x_4801_; lean_object* v___x_4802_; 
lean_del_object(v___x_4791_);
v_a_4797_ = lean_ctor_get(v_a_4789_, 0);
lean_inc(v_a_4797_);
lean_dec_ref_known(v_a_4789_, 1);
v___x_4798_ = lean_box(0);
v___x_4799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
lean_ctor_set(v___x_4799_, 1, v_a_4797_);
v_sz_4800_ = lean_array_size(v_tail_4787_);
v___x_4801_ = ((size_t)0ULL);
v___x_4802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_tail_4787_, v_sz_4800_, v___x_4801_, v___x_4799_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4816_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4805_ = v___x_4802_;
v_isShared_4806_ = v_isSharedCheck_4816_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4802_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4816_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v_fst_4807_; 
v_fst_4807_ = lean_ctor_get(v_a_4803_, 0);
if (lean_obj_tag(v_fst_4807_) == 0)
{
lean_object* v_snd_4808_; lean_object* v___x_4810_; 
v_snd_4808_ = lean_ctor_get(v_a_4803_, 1);
lean_inc(v_snd_4808_);
lean_dec(v_a_4803_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 0, v_snd_4808_);
v___x_4810_ = v___x_4805_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_snd_4808_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
else
{
lean_object* v_val_4812_; lean_object* v___x_4814_; 
lean_inc_ref(v_fst_4807_);
lean_dec(v_a_4803_);
v_val_4812_ = lean_ctor_get(v_fst_4807_, 0);
lean_inc(v_val_4812_);
lean_dec_ref_known(v_fst_4807_, 1);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 0, v_val_4812_);
v___x_4814_ = v___x_4805_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_val_4812_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
}
else
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
v_a_4817_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4802_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4802_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
v_a_4826_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4788_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4788_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_4834_, lean_object* v_init_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_t_4834_, v_init_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec_ref(v_t_4834_);
return v_res_4847_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4850_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1));
v___x_4851_ = lean_unsigned_to_nat(2u);
v___x_4852_ = lean_unsigned_to_nat(103u);
v___x_4853_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0));
v___x_4854_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_4855_ = l_mkPanicMessageWithDecl(v___x_4854_, v___x_4853_, v___x_4852_, v___x_4851_, v___x_4850_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4856_, v_a_4864_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v_vars_4869_; lean_object* v_diseqs_4870_; lean_object* v_size_4871_; lean_object* v_size_4872_; uint8_t v___x_4873_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
lean_inc(v_a_4868_);
lean_dec_ref_known(v___x_4867_, 1);
v_vars_4869_ = lean_ctor_get(v_a_4868_, 0);
lean_inc_ref(v_vars_4869_);
v_diseqs_4870_ = lean_ctor_get(v_a_4868_, 8);
lean_inc_ref(v_diseqs_4870_);
lean_dec(v_a_4868_);
v_size_4871_ = lean_ctor_get(v_vars_4869_, 2);
lean_inc(v_size_4871_);
lean_dec_ref(v_vars_4869_);
v_size_4872_ = lean_ctor_get(v_diseqs_4870_, 2);
v___x_4873_ = lean_nat_dec_eq(v_size_4871_, v_size_4872_);
lean_dec(v_size_4871_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
lean_dec_ref(v_diseqs_4870_);
v___x_4874_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2);
v___x_4875_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_4874_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
return v___x_4875_;
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = lean_unsigned_to_nat(0u);
v___x_4877_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_diseqs_4870_, v___x_4876_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
lean_dec_ref(v_diseqs_4870_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4885_; 
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4885_ == 0)
{
lean_object* v_unused_4886_; 
v_unused_4886_ = lean_ctor_get(v___x_4877_, 0);
lean_dec(v_unused_4886_);
v___x_4879_ = v___x_4877_;
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
else
{
lean_dec(v___x_4877_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4881_ = lean_box(0);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 0, v___x_4881_);
v___x_4883_ = v___x_4879_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
v_a_4887_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4877_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4877_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
v_a_4895_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4867_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4867_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___boxed(lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
lean_dec(v_a_4910_);
lean_dec_ref(v_a_4909_);
lean_dec(v_a_4908_);
lean_dec_ref(v_a_4907_);
lean_dec(v_a_4906_);
lean_dec_ref(v_a_4905_);
lean_dec(v_a_4904_);
lean_dec(v_a_4903_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v___x_4927_; 
lean_dec_ref_known(v___x_4926_, 1);
v___x_4927_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v___x_4928_; 
lean_dec_ref_known(v___x_4927_, 1);
v___x_4928_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v___x_4929_; 
lean_dec_ref_known(v___x_4928_, 1);
v___x_4929_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v___x_4930_; 
lean_dec_ref_known(v___x_4929_, 1);
v___x_4930_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v___x_4931_; 
lean_dec_ref_known(v___x_4930_, 1);
v___x_4931_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v___x_4932_; 
lean_dec_ref_known(v___x_4931_, 1);
v___x_4932_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
return v___x_4932_;
}
else
{
return v___x_4931_;
}
}
else
{
return v___x_4930_;
}
}
else
{
return v___x_4929_;
}
}
else
{
return v___x_4928_;
}
}
else
{
return v___x_4927_;
}
}
else
{
return v___x_4926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v_a_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v_a_4936_);
lean_dec_ref(v_a_4935_);
lean_dec(v_a_4934_);
lean_dec(v_a_4933_);
return v_res_4944_;
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
