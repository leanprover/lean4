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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
lean_object* v_k_5_; lean_object* v_p_6_; lean_object* v___x_7_; uint8_t v___x_8_; uint8_t v___x_9_; 
v_k_5_ = lean_ctor_get(v_x_3_, 0);
v_p_6_ = lean_ctor_get(v_x_3_, 2);
v___x_7_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_8_ = lean_int_dec_eq(v_k_5_, v___x_7_);
v___x_9_ = lean_bool_not(v___x_8_);
if (v___x_9_ == 0)
{
return v___x_9_;
}
else
{
v_x_3_ = v_p_6_;
goto _start;
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
lean_object* v___x_27_; lean_object* v___x_1513__overap_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0, &l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0_once, _init_l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0___closed__0);
v___x_1513__overap_28_ = lean_panic_fn_borrowed(v___x_27_, v_msg_15_);
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
v___x_29_ = lean_apply_11(v___x_1513__overap_28_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, lean_box(0));
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
lean_object* v_a_67_; uint8_t v___x_68_; uint8_t v___x_69_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = lean_unbox(v_a_67_);
lean_dec(v_a_67_);
v___x_69_ = lean_bool_not(v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3, &l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3_once, _init_l_Int_Internal_Linear_Poly_checkNoElimVars___closed__3);
v___x_71_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_70_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
return v___x_71_;
}
else
{
v_p_52_ = v_p_65_;
goto _start;
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_a_73_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_66_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_66_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_box(0);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkNoElimVars___boxed(lean_object* v_p_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Int_Internal_Linear_Poly_checkNoElimVars(v_p_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_p_83_);
return v_res_95_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(lean_object* v_k_96_, lean_object* v_t_97_){
_start:
{
if (lean_obj_tag(v_t_97_) == 0)
{
lean_object* v_k_98_; lean_object* v_l_99_; lean_object* v_r_100_; uint8_t v___x_101_; 
v_k_98_ = lean_ctor_get(v_t_97_, 1);
v_l_99_ = lean_ctor_get(v_t_97_, 3);
v_r_100_ = lean_ctor_get(v_t_97_, 4);
v___x_101_ = lean_nat_dec_lt(v_k_96_, v_k_98_);
if (v___x_101_ == 0)
{
uint8_t v___x_102_; 
v___x_102_ = lean_nat_dec_eq(v_k_96_, v_k_98_);
if (v___x_102_ == 0)
{
v_t_97_ = v_r_100_;
goto _start;
}
else
{
return v___x_102_;
}
}
else
{
v_t_97_ = v_l_99_;
goto _start;
}
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg___boxed(lean_object* v_k_106_, lean_object* v_t_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_106_, v_t_107_);
lean_dec(v_t_107_);
lean_dec(v_k_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__1));
v___x_113_ = lean_unsigned_to_nat(4u);
v___x_114_ = lean_unsigned_to_nat(30u);
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__0));
v___x_116_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_117_ = l_mkPanicMessageWithDecl(v___x_116_, v___x_115_, v___x_114_, v___x_113_, v___x_112_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(lean_object* v_y_118_, lean_object* v_p_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
if (lean_obj_tag(v_p_119_) == 1)
{
lean_object* v_v_131_; lean_object* v_p_132_; lean_object* v___x_133_; 
v_v_131_ = lean_ctor_get(v_p_119_, 1);
v_p_132_ = lean_ctor_get(v_p_119_, 2);
v___x_133_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_v_131_, v_a_120_, v_a_128_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; uint8_t v___x_135_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_y_118_, v_a_134_);
lean_dec(v_a_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___closed__2);
v___x_137_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_136_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
return v___x_137_;
}
else
{
v_p_119_ = v_p_132_;
goto _start;
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_133_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_133_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go___boxed(lean_object* v_y_149_, lean_object* v_p_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(v_y_149_, v_p_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_p_150_);
lean_dec(v_y_149_);
return v_res_162_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0(lean_object* v_00_u03b2_163_, lean_object* v_k_164_, lean_object* v_t_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_164_, v_t_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0___boxed(lean_object* v_00_u03b2_167_, lean_object* v_k_168_, lean_object* v_t_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go_spec__0(v_00_u03b2_167_, v_k_168_, v_t_169_);
lean_dec(v_t_169_);
lean_dec(v_k_168_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkOccs(lean_object* v_p_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
if (lean_obj_tag(v_p_172_) == 1)
{
lean_object* v_v_184_; lean_object* v_p_185_; lean_object* v___x_186_; 
v_v_184_ = lean_ctor_get(v_p_172_, 1);
v_p_185_ = lean_ctor_get(v_p_172_, 2);
v___x_186_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Internal_Linear_Poly_checkOccs_go(v_v_184_, v_p_185_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkOccs___boxed(lean_object* v_p_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Int_Internal_Linear_Poly_checkOccs(v_p_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_p_189_);
return v_res_201_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_204_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__1));
v___x_205_ = lean_unsigned_to_nat(2u);
v___x_206_ = lean_unsigned_to_nat(41u);
v___x_207_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_208_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_209_ = l_mkPanicMessageWithDecl(v___x_208_, v___x_207_, v___x_206_, v___x_205_, v___x_204_);
return v___x_209_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_211_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_212_ = lean_unsigned_to_nat(24u);
v___x_213_ = lean_unsigned_to_nat(40u);
v___x_214_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_215_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_216_ = l_mkPanicMessageWithDecl(v___x_215_, v___x_214_, v___x_213_, v___x_212_, v___x_211_);
return v___x_216_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_218_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__5));
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = lean_unsigned_to_nat(35u);
v___x_221_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_222_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_223_ = l_mkPanicMessageWithDecl(v___x_222_, v___x_221_, v___x_220_, v___x_219_, v___x_218_);
return v___x_223_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_225_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__7));
v___x_226_ = lean_unsigned_to_nat(2u);
v___x_227_ = lean_unsigned_to_nat(36u);
v___x_228_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__0));
v___x_229_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_230_ = l_mkPanicMessageWithDecl(v___x_229_, v___x_228_, v___x_227_, v___x_226_, v___x_225_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf(lean_object* v_p_231_, lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; uint8_t v___x_263_; 
v___x_263_ = l_Int_Internal_Linear_Poly_isSorted(v_p_231_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__6);
v___x_265_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_264_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
return v___x_265_;
}
else
{
uint8_t v___x_266_; 
v___x_266_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_231_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__8);
v___x_268_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_267_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_233_, v_a_241_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; uint8_t v___x_271_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
v___x_271_ = lean_unbox(v_a_270_);
lean_dec(v_a_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = l_Int_Internal_Linear_Poly_checkNoElimVars(v_p_231_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v___x_273_; 
lean_dec_ref_known(v___x_272_, 1);
v___x_273_ = l_Int_Internal_Linear_Poly_checkOccs(v_p_231_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_dec_ref_known(v___x_273_, 1);
v___y_245_ = v_a_233_;
v___y_246_ = v_a_234_;
v___y_247_ = v_a_235_;
v___y_248_ = v_a_236_;
v___y_249_ = v_a_237_;
v___y_250_ = v_a_238_;
v___y_251_ = v_a_239_;
v___y_252_ = v_a_240_;
v___y_253_ = v_a_241_;
v___y_254_ = v_a_242_;
goto v___jp_244_;
}
else
{
return v___x_273_;
}
}
else
{
return v___x_272_;
}
}
else
{
v___y_245_ = v_a_233_;
v___y_246_ = v_a_234_;
v___y_247_ = v_a_235_;
v___y_248_ = v_a_236_;
v___y_249_ = v_a_237_;
v___y_250_ = v_a_238_;
v___y_251_ = v_a_239_;
v___y_252_ = v_a_240_;
v___y_253_ = v_a_241_;
v___y_254_ = v_a_242_;
goto v___jp_244_;
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_269_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_269_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
v___jp_244_:
{
if (lean_obj_tag(v_p_231_) == 1)
{
lean_object* v_v_255_; uint8_t v___x_256_; 
v_v_255_ = lean_ctor_get(v_p_231_, 1);
v___x_256_ = lean_nat_dec_eq(v_x_232_, v_v_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__2);
v___x_258_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_257_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4, &l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4_once, _init_l_Int_Internal_Linear_Poly_checkCnstrOf___closed__4);
v___x_262_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_261_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_checkCnstrOf___boxed(lean_object* v_p_282_, lean_object* v_x_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_282_, v_x_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec(v_a_284_);
lean_dec(v_x_283_);
lean_dec_ref(v_p_282_);
return v_res_295_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_4051__overap_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0);
v___x_4051__overap_310_ = lean_panic_fn_borrowed(v___x_309_, v_msg_297_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
lean_inc(v___y_299_);
lean_inc(v___y_298_);
v___x_311_ = lean_apply_11(v___x_4051__overap_310_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, lean_box(0));
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___boxed(lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v_msg_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec(v___y_313_);
return v_res_324_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1));
v___x_328_ = lean_unsigned_to_nat(6u);
v___x_329_ = lean_unsigned_to_nat(49u);
v___x_330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_331_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_332_ = l_mkPanicMessageWithDecl(v___x_331_, v___x_330_, v___x_329_, v___x_328_, v___x_327_);
return v___x_332_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_333_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_334_ = lean_unsigned_to_nat(30u);
v___x_335_ = lean_unsigned_to_nat(48u);
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0));
v___x_337_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_338_ = l_mkPanicMessageWithDecl(v___x_337_, v___x_336_, v___x_335_, v___x_334_, v___x_333_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(lean_object* v_____s_339_, uint8_t v_isLower_340_, lean_object* v_as_341_, size_t v_sz_342_, size_t v_i_343_, lean_object* v_b_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = lean_usize_dec_lt(v_i_343_, v_sz_342_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_b_344_);
return v___x_357_;
}
else
{
lean_object* v_snd_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_434_; 
v_snd_358_ = lean_ctor_get(v_b_344_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_b_344_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v_b_344_, 0);
lean_dec(v_unused_435_);
v___x_360_ = v_b_344_;
v_isShared_361_ = v_isSharedCheck_434_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_snd_358_);
lean_dec(v_b_344_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_434_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_a_362_; lean_object* v_p_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_432_; 
v_a_362_ = lean_array_uget(v_as_341_, v_i_343_);
v_p_363_ = lean_ctor_get(v_a_362_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_a_362_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v_a_362_, 1);
lean_dec(v_unused_433_);
v___x_365_ = v_a_362_;
v_isShared_366_ = v_isSharedCheck_432_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_p_363_);
lean_dec(v_a_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_432_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; 
v___x_367_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_363_, v_____s_339_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v___x_368_; lean_object* v_a_370_; lean_object* v___x_408_; uint8_t v___y_410_; 
lean_dec_ref_known(v___x_367_, 1);
v___x_368_ = lean_box(0);
v___x_408_ = lean_box(0);
if (lean_obj_tag(v_p_363_) == 1)
{
lean_object* v_k_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_k_411_ = lean_ctor_get(v_p_363_, 0);
lean_inc(v_k_411_);
lean_dec_ref_known(v_p_363_, 3);
v___x_412_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_413_ = lean_int_dec_lt(v_k_411_, v___x_412_);
lean_dec(v_k_411_);
if (v_isLower_340_ == 0)
{
if (v___x_413_ == 0)
{
v___y_410_ = v___x_356_;
goto v___jp_409_;
}
else
{
goto v___jp_377_;
}
}
else
{
v___y_410_ = v___x_413_;
goto v___jp_409_;
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_del_object(v___x_365_);
lean_dec_ref(v_p_363_);
lean_dec(v_snd_358_);
v___x_414_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_415_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_414_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_dec_ref_known(v___x_415_, 1);
v_a_370_ = v___x_408_;
goto v___jp_369_;
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_del_object(v___x_360_);
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
v___jp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_a_370_);
lean_ctor_set(v___x_360_, 0, v___x_368_);
v___x_372_ = v___x_360_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_a_370_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
size_t v___x_373_; size_t v___x_374_; 
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_343_, v___x_373_);
v_i_343_ = v___x_374_;
v_b_344_ = v___x_372_;
goto _start;
}
}
v___jp_377_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_379_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_378_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_399_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_399_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_399_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_399_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
if (lean_obj_tag(v_a_380_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_397_; 
lean_del_object(v___x_360_);
v_a_384_ = lean_ctor_get(v_a_380_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v_a_380_);
if (v_isSharedCheck_397_ == 0)
{
v___x_386_ = v_a_380_;
v_isShared_387_ = v_isSharedCheck_397_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v_a_380_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_397_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 1);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_396_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_391_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v_snd_358_);
lean_ctor_set(v___x_365_, 0, v___x_389_);
v___x_391_ = v___x_365_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_snd_358_);
v___x_391_ = v_reuseFailAlloc_395_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_391_);
v___x_393_ = v___x_382_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_object* v_a_398_; 
lean_del_object(v___x_382_);
lean_del_object(v___x_365_);
lean_dec(v_snd_358_);
v_a_398_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v_a_380_, 1);
v_a_370_ = v_a_398_;
goto v___jp_369_;
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_del_object(v___x_365_);
lean_del_object(v___x_360_);
lean_dec(v_snd_358_);
v_a_400_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_379_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_379_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
v___jp_409_:
{
if (v___y_410_ == 0)
{
goto v___jp_377_;
}
else
{
lean_del_object(v___x_365_);
lean_dec(v_snd_358_);
v_a_370_ = v___x_408_;
goto v___jp_369_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_del_object(v___x_365_);
lean_dec_ref(v_p_363_);
lean_del_object(v___x_360_);
lean_dec(v_snd_358_);
v_a_424_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_367_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_367_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_____s_436_ = _args[0];
lean_object* v_isLower_437_ = _args[1];
lean_object* v_as_438_ = _args[2];
lean_object* v_sz_439_ = _args[3];
lean_object* v_i_440_ = _args[4];
lean_object* v_b_441_ = _args[5];
lean_object* v___y_442_ = _args[6];
lean_object* v___y_443_ = _args[7];
lean_object* v___y_444_ = _args[8];
lean_object* v___y_445_ = _args[9];
lean_object* v___y_446_ = _args[10];
lean_object* v___y_447_ = _args[11];
lean_object* v___y_448_ = _args[12];
lean_object* v___y_449_ = _args[13];
lean_object* v___y_450_ = _args[14];
lean_object* v___y_451_ = _args[15];
lean_object* v___y_452_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_453_; size_t v_sz_boxed_454_; size_t v_i_boxed_455_; lean_object* v_res_456_; 
v_isLower_boxed_453_ = lean_unbox(v_isLower_437_);
v_sz_boxed_454_ = lean_unbox_usize(v_sz_439_);
lean_dec(v_sz_439_);
v_i_boxed_455_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_res_456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_436_, v_isLower_boxed_453_, v_as_438_, v_sz_boxed_454_, v_i_boxed_455_, v_b_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v_as_438_);
lean_dec(v_____s_436_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(lean_object* v_____s_457_, uint8_t v_isLower_458_, lean_object* v_as_459_, size_t v_sz_460_, size_t v_i_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = lean_usize_dec_lt(v_i_461_, v_sz_460_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v_b_462_);
return v___x_475_;
}
else
{
lean_object* v_snd_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_552_; 
v_snd_476_ = lean_ctor_get(v_b_462_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_b_462_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_b_462_, 0);
lean_dec(v_unused_553_);
v___x_478_ = v_b_462_;
v_isShared_479_ = v_isSharedCheck_552_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_snd_476_);
lean_dec(v_b_462_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_552_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_a_480_; lean_object* v_p_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_550_; 
v_a_480_ = lean_array_uget(v_as_459_, v_i_461_);
v_p_481_ = lean_ctor_get(v_a_480_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_a_480_, 1);
lean_dec(v_unused_551_);
v___x_483_ = v_a_480_;
v_isShared_484_ = v_isSharedCheck_550_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_p_481_);
lean_dec(v_a_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_550_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; 
v___x_485_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_481_, v_____s_457_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_a_489_; uint8_t v___y_528_; 
lean_dec_ref_known(v___x_485_, 1);
v___x_486_ = lean_box(0);
v___x_487_ = lean_box(0);
if (lean_obj_tag(v_p_481_) == 1)
{
lean_object* v_k_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_k_529_ = lean_ctor_get(v_p_481_, 0);
lean_inc(v_k_529_);
lean_dec_ref_known(v_p_481_, 3);
v___x_530_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_531_ = lean_int_dec_lt(v_k_529_, v___x_530_);
lean_dec(v_k_529_);
if (v_isLower_458_ == 0)
{
if (v___x_531_ == 0)
{
v___y_528_ = v___x_474_;
goto v___jp_527_;
}
else
{
goto v___jp_496_;
}
}
else
{
v___y_528_ = v___x_531_;
goto v___jp_527_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_del_object(v___x_483_);
lean_dec_ref(v_p_481_);
lean_dec(v_snd_476_);
v___x_532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_533_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_532_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec_ref_known(v___x_533_, 1);
v_a_489_ = v___x_486_;
goto v___jp_488_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_del_object(v___x_478_);
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
v___jp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_a_489_);
lean_ctor_set(v___x_478_, 0, v___x_487_);
v___x_491_ = v___x_478_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_489_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_461_, v___x_492_);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_457_, v_isLower_458_, v_as_459_, v_sz_460_, v___x_493_, v___x_491_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v___x_494_;
}
}
v___jp_496_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_498_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_497_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_518_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_518_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_518_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_518_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
if (lean_obj_tag(v_a_499_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_516_; 
lean_del_object(v___x_478_);
v_a_503_ = lean_ctor_get(v_a_499_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_516_ == 0)
{
v___x_505_ = v_a_499_;
v_isShared_506_ = v_isSharedCheck_516_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v_a_499_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_516_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 1);
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_515_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_510_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v_snd_476_);
lean_ctor_set(v___x_483_, 0, v___x_508_);
v___x_510_ = v___x_483_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_snd_476_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_510_);
v___x_512_ = v___x_501_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
else
{
lean_object* v_a_517_; 
lean_del_object(v___x_501_);
lean_del_object(v___x_483_);
lean_dec(v_snd_476_);
v_a_517_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v_a_499_, 1);
v_a_489_ = v_a_517_;
goto v___jp_488_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_483_);
lean_del_object(v___x_478_);
lean_dec(v_snd_476_);
v_a_519_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_498_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_498_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
v___jp_527_:
{
if (v___y_528_ == 0)
{
goto v___jp_496_;
}
else
{
lean_del_object(v___x_483_);
lean_dec(v_snd_476_);
v_a_489_ = v___x_486_;
goto v___jp_488_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_del_object(v___x_483_);
lean_dec_ref(v_p_481_);
lean_del_object(v___x_478_);
lean_dec(v_snd_476_);
v_a_542_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_485_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_485_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_____s_554_ = _args[0];
lean_object* v_isLower_555_ = _args[1];
lean_object* v_as_556_ = _args[2];
lean_object* v_sz_557_ = _args[3];
lean_object* v_i_558_ = _args[4];
lean_object* v_b_559_ = _args[5];
lean_object* v___y_560_ = _args[6];
lean_object* v___y_561_ = _args[7];
lean_object* v___y_562_ = _args[8];
lean_object* v___y_563_ = _args[9];
lean_object* v___y_564_ = _args[10];
lean_object* v___y_565_ = _args[11];
lean_object* v___y_566_ = _args[12];
lean_object* v___y_567_ = _args[13];
lean_object* v___y_568_ = _args[14];
lean_object* v___y_569_ = _args[15];
lean_object* v___y_570_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_571_; size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_isLower_boxed_571_ = lean_unbox(v_isLower_555_);
v_sz_boxed_572_ = lean_unbox_usize(v_sz_557_);
lean_dec(v_sz_557_);
v_i_boxed_573_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_554_, v_isLower_boxed_571_, v_as_556_, v_sz_boxed_572_, v_i_boxed_573_, v_b_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v_as_556_);
lean_dec(v_____s_554_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(lean_object* v_____s_575_, uint8_t v_isLower_576_, lean_object* v_as_577_, size_t v_sz_578_, size_t v_i_579_, lean_object* v_b_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = lean_usize_dec_lt(v_i_579_, v_sz_578_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v_b_580_);
return v___x_593_;
}
else
{
lean_object* v_snd_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_663_; 
v_snd_594_ = lean_ctor_get(v_b_580_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_b_580_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_b_580_, 0);
lean_dec(v_unused_664_);
v___x_596_ = v_b_580_;
v_isShared_597_ = v_isSharedCheck_663_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_snd_594_);
lean_dec(v_b_580_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_663_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_a_598_; lean_object* v_p_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_661_; 
v_a_598_ = lean_array_uget(v_as_577_, v_i_579_);
v_p_599_ = lean_ctor_get(v_a_598_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_a_598_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_a_598_, 1);
lean_dec(v_unused_662_);
v___x_601_ = v_a_598_;
v_isShared_602_ = v_isSharedCheck_661_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_p_599_);
lean_dec(v_a_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_661_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; 
v___x_603_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_599_, v_____s_575_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_604_; lean_object* v_a_606_; lean_object* v___x_637_; uint8_t v___y_639_; 
lean_dec_ref_known(v___x_603_, 1);
v___x_604_ = lean_box(0);
v___x_637_ = lean_box(0);
if (lean_obj_tag(v_p_599_) == 1)
{
lean_object* v_k_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_k_640_ = lean_ctor_get(v_p_599_, 0);
lean_inc(v_k_640_);
lean_dec_ref_known(v_p_599_, 3);
v___x_641_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_642_ = lean_int_dec_lt(v_k_640_, v___x_641_);
lean_dec(v_k_640_);
if (v_isLower_576_ == 0)
{
if (v___x_642_ == 0)
{
v___y_639_ = v___x_592_;
goto v___jp_638_;
}
else
{
goto v___jp_613_;
}
}
else
{
v___y_639_ = v___x_642_;
goto v___jp_638_;
}
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_del_object(v___x_601_);
lean_dec_ref(v_p_599_);
lean_dec(v_snd_594_);
v___x_643_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_644_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_643_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref_known(v___x_644_, 1);
v_a_606_ = v___x_637_;
goto v___jp_605_;
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_del_object(v___x_596_);
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
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
}
v___jp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v_a_606_);
lean_ctor_set(v___x_596_, 0, v___x_604_);
v___x_608_ = v___x_596_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_a_606_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
size_t v___x_609_; size_t v___x_610_; 
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_579_, v___x_609_);
v_i_579_ = v___x_610_;
v_b_580_ = v___x_608_;
goto _start;
}
}
v___jp_613_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_615_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_614_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_628_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
if (lean_obj_tag(v_a_616_) == 0)
{
lean_object* v___x_620_; lean_object* v___x_622_; 
lean_del_object(v___x_596_);
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v_a_616_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v_snd_594_);
lean_ctor_set(v___x_601_, 0, v___x_620_);
v___x_622_ = v___x_601_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_snd_594_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_622_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; 
lean_del_object(v___x_618_);
lean_del_object(v___x_601_);
lean_dec(v_snd_594_);
v_a_627_ = lean_ctor_get(v_a_616_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v_a_616_, 1);
v_a_606_ = v_a_627_;
goto v___jp_605_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_del_object(v___x_601_);
lean_del_object(v___x_596_);
lean_dec(v_snd_594_);
v_a_629_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_615_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_615_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
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
v___jp_638_:
{
if (v___y_639_ == 0)
{
goto v___jp_613_;
}
else
{
lean_del_object(v___x_601_);
lean_dec(v_snd_594_);
v_a_606_ = v___x_637_;
goto v___jp_605_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_del_object(v___x_601_);
lean_dec_ref(v_p_599_);
lean_del_object(v___x_596_);
lean_dec(v_snd_594_);
v_a_653_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_603_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_603_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_____s_665_ = _args[0];
lean_object* v_isLower_666_ = _args[1];
lean_object* v_as_667_ = _args[2];
lean_object* v_sz_668_ = _args[3];
lean_object* v_i_669_ = _args[4];
lean_object* v_b_670_ = _args[5];
lean_object* v___y_671_ = _args[6];
lean_object* v___y_672_ = _args[7];
lean_object* v___y_673_ = _args[8];
lean_object* v___y_674_ = _args[9];
lean_object* v___y_675_ = _args[10];
lean_object* v___y_676_ = _args[11];
lean_object* v___y_677_ = _args[12];
lean_object* v___y_678_ = _args[13];
lean_object* v___y_679_ = _args[14];
lean_object* v___y_680_ = _args[15];
lean_object* v___y_681_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_682_; size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_isLower_boxed_682_ = lean_unbox(v_isLower_666_);
v_sz_boxed_683_ = lean_unbox_usize(v_sz_668_);
lean_dec(v_sz_668_);
v_i_boxed_684_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_665_, v_isLower_boxed_682_, v_as_667_, v_sz_boxed_683_, v_i_boxed_684_, v_b_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v_as_667_);
lean_dec(v_____s_665_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(lean_object* v_____s_686_, uint8_t v_isLower_687_, lean_object* v_as_688_, size_t v_sz_689_, size_t v_i_690_, lean_object* v_b_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_lt(v_i_690_, v_sz_689_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v_b_691_);
return v___x_704_;
}
else
{
lean_object* v_snd_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_774_; 
v_snd_705_ = lean_ctor_get(v_b_691_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_b_691_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v_b_691_, 0);
lean_dec(v_unused_775_);
v___x_707_ = v_b_691_;
v_isShared_708_ = v_isSharedCheck_774_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snd_705_);
lean_dec(v_b_691_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_774_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_a_709_; lean_object* v_p_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_772_; 
v_a_709_ = lean_array_uget(v_as_688_, v_i_690_);
v_p_710_ = lean_ctor_get(v_a_709_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v_a_709_, 1);
lean_dec(v_unused_773_);
v___x_712_ = v_a_709_;
v_isShared_713_ = v_isSharedCheck_772_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_p_710_);
lean_dec(v_a_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_772_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; 
v___x_714_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_710_, v_____s_686_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_a_718_; uint8_t v___y_750_; 
lean_dec_ref_known(v___x_714_, 1);
v___x_715_ = lean_box(0);
v___x_716_ = lean_box(0);
if (lean_obj_tag(v_p_710_) == 1)
{
lean_object* v_k_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_k_751_ = lean_ctor_get(v_p_710_, 0);
lean_inc(v_k_751_);
lean_dec_ref_known(v_p_710_, 3);
v___x_752_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_753_ = lean_int_dec_lt(v_k_751_, v___x_752_);
lean_dec(v_k_751_);
if (v_isLower_687_ == 0)
{
if (v___x_753_ == 0)
{
v___y_750_ = v___x_703_;
goto v___jp_749_;
}
else
{
goto v___jp_725_;
}
}
else
{
v___y_750_ = v___x_753_;
goto v___jp_749_;
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_del_object(v___x_712_);
lean_dec_ref(v_p_710_);
lean_dec(v_snd_705_);
v___x_754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
v___x_755_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_754_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_dec_ref_known(v___x_755_, 1);
v_a_718_ = v___x_715_;
goto v___jp_717_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_del_object(v___x_707_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v_a_718_);
lean_ctor_set(v___x_707_, 0, v___x_716_);
v___x_720_ = v___x_707_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_a_718_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_690_, v___x_721_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_686_, v_isLower_687_, v_as_688_, v_sz_689_, v___x_722_, v___x_720_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_723_;
}
}
v___jp_725_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
v___x_727_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_726_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_740_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_740_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_740_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_740_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
if (lean_obj_tag(v_a_728_) == 0)
{
lean_object* v___x_732_; lean_object* v___x_734_; 
lean_del_object(v___x_707_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_a_728_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v_snd_705_);
lean_ctor_set(v___x_712_, 0, v___x_732_);
v___x_734_ = v___x_712_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_snd_705_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_a_739_; 
lean_del_object(v___x_730_);
lean_del_object(v___x_712_);
lean_dec(v_snd_705_);
v_a_739_ = lean_ctor_get(v_a_728_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v_a_728_, 1);
v_a_718_ = v_a_739_;
goto v___jp_717_;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_del_object(v___x_712_);
lean_del_object(v___x_707_);
lean_dec(v_snd_705_);
v_a_741_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_727_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_727_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
v___jp_749_:
{
if (v___y_750_ == 0)
{
goto v___jp_725_;
}
else
{
lean_del_object(v___x_712_);
lean_dec(v_snd_705_);
v_a_718_ = v___x_715_;
goto v___jp_717_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_del_object(v___x_712_);
lean_dec_ref(v_p_710_);
lean_del_object(v___x_707_);
lean_dec(v_snd_705_);
v_a_764_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_714_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_714_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_____s_776_ = _args[0];
lean_object* v_isLower_777_ = _args[1];
lean_object* v_as_778_ = _args[2];
lean_object* v_sz_779_ = _args[3];
lean_object* v_i_780_ = _args[4];
lean_object* v_b_781_ = _args[5];
lean_object* v___y_782_ = _args[6];
lean_object* v___y_783_ = _args[7];
lean_object* v___y_784_ = _args[8];
lean_object* v___y_785_ = _args[9];
lean_object* v___y_786_ = _args[10];
lean_object* v___y_787_ = _args[11];
lean_object* v___y_788_ = _args[12];
lean_object* v___y_789_ = _args[13];
lean_object* v___y_790_ = _args[14];
lean_object* v___y_791_ = _args[15];
lean_object* v___y_792_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_793_; size_t v_sz_boxed_794_; size_t v_i_boxed_795_; lean_object* v_res_796_; 
v_isLower_boxed_793_ = lean_unbox(v_isLower_777_);
v_sz_boxed_794_ = lean_unbox_usize(v_sz_779_);
lean_dec(v_sz_779_);
v_i_boxed_795_ = lean_unbox_usize(v_i_780_);
lean_dec(v_i_780_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_776_, v_isLower_boxed_793_, v_as_778_, v_sz_boxed_794_, v_i_boxed_795_, v_b_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v_as_778_);
lean_dec(v_____s_776_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(lean_object* v_init_797_, lean_object* v_____s_798_, uint8_t v_isLower_799_, lean_object* v_n_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
if (lean_obj_tag(v_n_800_) == 0)
{
lean_object* v_cs_813_; lean_object* v___x_814_; lean_object* v___x_815_; size_t v_sz_816_; size_t v___x_817_; lean_object* v___x_818_; 
v_cs_813_ = lean_ctor_get(v_n_800_, 0);
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v_b_801_);
v_sz_816_ = lean_array_size(v_cs_813_);
v___x_817_ = ((size_t)0ULL);
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_797_, v_____s_798_, v_isLower_799_, v_cs_813_, v_sz_816_, v___x_817_, v___x_815_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_833_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_833_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_833_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_833_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_fst_823_; 
v_fst_823_ = lean_ctor_get(v_a_819_, 0);
if (lean_obj_tag(v_fst_823_) == 0)
{
lean_object* v_snd_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v_snd_824_ = lean_ctor_get(v_a_819_, 1);
lean_inc(v_snd_824_);
lean_dec(v_a_819_);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v_snd_824_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_825_);
v___x_827_ = v___x_821_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v_val_829_; lean_object* v___x_831_; 
lean_inc_ref(v_fst_823_);
lean_dec(v_a_819_);
v_val_829_ = lean_ctor_get(v_fst_823_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_fst_823_, 1);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v_val_829_);
v___x_831_ = v___x_821_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_val_829_);
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
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_834_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_818_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_818_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v_vs_842_; lean_object* v___x_843_; lean_object* v___x_844_; size_t v_sz_845_; size_t v___x_846_; lean_object* v___x_847_; 
v_vs_842_ = lean_ctor_get(v_n_800_, 0);
v___x_843_ = lean_box(0);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_b_801_);
v_sz_845_ = lean_array_size(v_vs_842_);
v___x_846_ = ((size_t)0ULL);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_798_, v_isLower_799_, v_vs_842_, v_sz_845_, v___x_846_, v___x_844_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_862_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_862_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_862_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_862_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_fst_852_; 
v_fst_852_ = lean_ctor_get(v_a_848_, 0);
if (lean_obj_tag(v_fst_852_) == 0)
{
lean_object* v_snd_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v_snd_853_ = lean_ctor_get(v_a_848_, 1);
lean_inc(v_snd_853_);
lean_dec(v_a_848_);
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v_snd_853_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_854_);
v___x_856_ = v___x_850_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
lean_object* v_val_858_; lean_object* v___x_860_; 
lean_inc_ref(v_fst_852_);
lean_dec(v_a_848_);
v_val_858_ = lean_ctor_get(v_fst_852_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v_fst_852_, 1);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v_val_858_);
v___x_860_ = v___x_850_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_val_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_847_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_847_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(lean_object* v_init_871_, lean_object* v_____s_872_, uint8_t v_isLower_873_, lean_object* v_as_874_, size_t v_sz_875_, size_t v_i_876_, lean_object* v_b_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v___x_889_; 
v___x_889_ = lean_usize_dec_lt(v_i_876_, v_sz_875_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v_b_877_);
return v___x_890_;
}
else
{
lean_object* v_snd_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_925_; 
v_snd_891_ = lean_ctor_get(v_b_877_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_b_877_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v_b_877_, 0);
lean_dec(v_unused_926_);
v___x_893_ = v_b_877_;
v_isShared_894_ = v_isSharedCheck_925_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_snd_891_);
lean_dec(v_b_877_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_925_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_array_uget_borrowed(v_as_874_, v_i_876_);
lean_inc(v_snd_891_);
v___x_896_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_871_, v_____s_872_, v_isLower_873_, v_a_895_, v_snd_891_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_916_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_916_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_916_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_916_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
if (lean_obj_tag(v_a_897_) == 0)
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_901_, 0, v_a_897_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_901_);
v___x_903_ = v___x_893_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_snd_891_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_905_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_903_);
v___x_905_ = v___x_899_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
lean_del_object(v___x_899_);
lean_dec(v_snd_891_);
v_a_908_ = lean_ctor_get(v_a_897_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v_a_897_, 1);
v___x_909_ = lean_box(0);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v_a_908_);
lean_ctor_set(v___x_893_, 0, v___x_909_);
v___x_911_ = v___x_893_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_a_908_);
v___x_911_ = v_reuseFailAlloc_915_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
size_t v___x_912_; size_t v___x_913_; 
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_add(v_i_876_, v___x_912_);
v_i_876_ = v___x_913_;
v_b_877_ = v___x_911_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_del_object(v___x_893_);
lean_dec(v_snd_891_);
v_a_917_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_896_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_896_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_927_ = _args[0];
lean_object* v_____s_928_ = _args[1];
lean_object* v_isLower_929_ = _args[2];
lean_object* v_as_930_ = _args[3];
lean_object* v_sz_931_ = _args[4];
lean_object* v_i_932_ = _args[5];
lean_object* v_b_933_ = _args[6];
lean_object* v___y_934_ = _args[7];
lean_object* v___y_935_ = _args[8];
lean_object* v___y_936_ = _args[9];
lean_object* v___y_937_ = _args[10];
lean_object* v___y_938_ = _args[11];
lean_object* v___y_939_ = _args[12];
lean_object* v___y_940_ = _args[13];
lean_object* v___y_941_ = _args[14];
lean_object* v___y_942_ = _args[15];
lean_object* v___y_943_ = _args[16];
lean_object* v___y_944_ = _args[17];
_start:
{
uint8_t v_isLower_boxed_945_; size_t v_sz_boxed_946_; size_t v_i_boxed_947_; lean_object* v_res_948_; 
v_isLower_boxed_945_ = lean_unbox(v_isLower_929_);
v_sz_boxed_946_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_947_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_927_, v_____s_928_, v_isLower_boxed_945_, v_as_930_, v_sz_boxed_946_, v_i_boxed_947_, v_b_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v_as_930_);
lean_dec(v_____s_928_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1___boxed(lean_object* v_init_949_, lean_object* v_____s_950_, lean_object* v_isLower_951_, lean_object* v_n_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
uint8_t v_isLower_boxed_965_; lean_object* v_res_966_; 
v_isLower_boxed_965_ = lean_unbox(v_isLower_951_);
v_res_966_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_949_, v_____s_950_, v_isLower_boxed_965_, v_n_952_, v_b_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v_n_952_);
lean_dec(v_____s_950_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(lean_object* v_____s_967_, uint8_t v_isLower_968_, lean_object* v_t_969_, lean_object* v_init_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_root_982_; lean_object* v_tail_983_; lean_object* v___x_984_; 
v_root_982_ = lean_ctor_get(v_t_969_, 0);
v_tail_983_ = lean_ctor_get(v_t_969_, 1);
v___x_984_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_970_, v_____s_967_, v_isLower_968_, v_root_982_, v_init_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1021_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_1021_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1021_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
if (lean_obj_tag(v_a_985_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; 
v_a_989_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v_a_985_, 1);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_a_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; size_t v_sz_996_; size_t v___x_997_; lean_object* v___x_998_; 
lean_del_object(v___x_987_);
v_a_993_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v_a_985_, 1);
v___x_994_ = lean_box(0);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_a_993_);
v_sz_996_ = lean_array_size(v_tail_983_);
v___x_997_ = ((size_t)0ULL);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_967_, v_isLower_968_, v_tail_983_, v_sz_996_, v___x_997_, v___x_995_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1012_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_fst_1003_; 
v_fst_1003_ = lean_ctor_get(v_a_999_, 0);
if (lean_obj_tag(v_fst_1003_) == 0)
{
lean_object* v_snd_1004_; lean_object* v___x_1006_; 
v_snd_1004_ = lean_ctor_get(v_a_999_, 1);
lean_inc(v_snd_1004_);
lean_dec(v_a_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_snd_1004_);
v___x_1006_ = v___x_1001_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_snd_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
lean_inc_ref(v_fst_1003_);
lean_dec(v_a_999_);
v_val_1008_ = lean_ctor_get(v_fst_1003_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v_fst_1003_, 1);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_val_1008_);
v___x_1010_ = v___x_1001_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_val_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_998_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_998_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_984_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_984_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1___boxed(lean_object* v_____s_1030_, lean_object* v_isLower_1031_, lean_object* v_t_1032_, lean_object* v_init_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v_isLower_boxed_1045_; lean_object* v_res_1046_; 
v_isLower_boxed_1045_ = lean_unbox(v_isLower_1031_);
v_res_1046_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_____s_1030_, v_isLower_boxed_1045_, v_t_1032_, v_init_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v_t_1032_);
lean_dec(v_____s_1030_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(uint8_t v_isLower_1047_, lean_object* v_as_1048_, size_t v_sz_1049_, size_t v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_usize_dec_lt(v_i_1050_, v_sz_1049_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_b_1051_);
return v___x_1064_;
}
else
{
lean_object* v_snd_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1089_; 
v_snd_1065_ = lean_ctor_get(v_b_1051_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_b_1051_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v_b_1051_, 0);
lean_dec(v_unused_1090_);
v___x_1067_ = v_b_1051_;
v_isShared_1068_ = v_isSharedCheck_1089_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_snd_1065_);
lean_dec(v_b_1051_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1089_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_a_1069_ = lean_array_uget_borrowed(v_as_1048_, v_i_1050_);
v___x_1070_ = lean_box(0);
v___x_1071_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1065_, v_isLower_1047_, v_a_1069_, v___x_1070_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
lean_dec_ref_known(v___x_1071_, 1);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = lean_nat_add(v_snd_1065_, v___x_1073_);
lean_dec(v_snd_1065_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 1, v___x_1074_);
lean_ctor_set(v___x_1067_, 0, v___x_1072_);
v___x_1076_ = v___x_1067_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
size_t v___x_1077_; size_t v___x_1078_; 
v___x_1077_ = ((size_t)1ULL);
v___x_1078_ = lean_usize_add(v_i_1050_, v___x_1077_);
v_i_1050_ = v___x_1078_;
v_b_1051_ = v___x_1076_;
goto _start;
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_del_object(v___x_1067_);
lean_dec(v_snd_1065_);
v_a_1081_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1071_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1071_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(lean_object* v_isLower_1091_, lean_object* v_as_1092_, lean_object* v_sz_1093_, lean_object* v_i_1094_, lean_object* v_b_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
uint8_t v_isLower_boxed_1107_; size_t v_sz_boxed_1108_; size_t v_i_boxed_1109_; lean_object* v_res_1110_; 
v_isLower_boxed_1107_ = lean_unbox(v_isLower_1091_);
v_sz_boxed_1108_ = lean_unbox_usize(v_sz_1093_);
lean_dec(v_sz_1093_);
v_i_boxed_1109_ = lean_unbox_usize(v_i_1094_);
lean_dec(v_i_1094_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_1107_, v_as_1092_, v_sz_boxed_1108_, v_i_boxed_1109_, v_b_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v_as_1092_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(uint8_t v_isLower_1111_, lean_object* v_as_1112_, size_t v_sz_1113_, size_t v_i_1114_, lean_object* v_b_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_usize_dec_lt(v_i_1114_, v_sz_1113_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_b_1115_);
return v___x_1128_;
}
else
{
lean_object* v_snd_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1153_; 
v_snd_1129_ = lean_ctor_get(v_b_1115_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_b_1115_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v_b_1115_, 0);
lean_dec(v_unused_1154_);
v___x_1131_ = v_b_1115_;
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_snd_1129_);
lean_dec(v_b_1115_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_a_1133_ = lean_array_uget_borrowed(v_as_1112_, v_i_1114_);
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1129_, v_isLower_1111_, v_a_1133_, v___x_1134_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_dec_ref_known(v___x_1135_, 1);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_add(v_snd_1129_, v___x_1137_);
lean_dec(v_snd_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v___x_1138_);
lean_ctor_set(v___x_1131_, 0, v___x_1136_);
v___x_1140_ = v___x_1131_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1114_, v___x_1141_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_1111_, v_as_1112_, v_sz_1113_, v___x_1142_, v___x_1140_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1143_;
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_1131_);
lean_dec(v_snd_1129_);
v_a_1145_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1135_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1135_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5___boxed(lean_object* v_isLower_1155_, lean_object* v_as_1156_, lean_object* v_sz_1157_, lean_object* v_i_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v_isLower_boxed_1171_; size_t v_sz_boxed_1172_; size_t v_i_boxed_1173_; lean_object* v_res_1174_; 
v_isLower_boxed_1171_ = lean_unbox(v_isLower_1155_);
v_sz_boxed_1172_ = lean_unbox_usize(v_sz_1157_);
lean_dec(v_sz_1157_);
v_i_boxed_1173_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_1171_, v_as_1156_, v_sz_boxed_1172_, v_i_boxed_1173_, v_b_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v_as_1156_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(uint8_t v_isLower_1175_, lean_object* v_as_1176_, size_t v_sz_1177_, size_t v_i_1178_, lean_object* v_b_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v___x_1191_; 
v___x_1191_ = lean_usize_dec_lt(v_i_1178_, v_sz_1177_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_b_1179_);
return v___x_1192_;
}
else
{
lean_object* v_snd_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1217_; 
v_snd_1193_ = lean_ctor_get(v_b_1179_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_b_1179_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_b_1179_, 0);
lean_dec(v_unused_1218_);
v___x_1195_ = v_b_1179_;
v_isShared_1196_ = v_isSharedCheck_1217_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_snd_1193_);
lean_dec(v_b_1179_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1217_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_a_1197_ = lean_array_uget_borrowed(v_as_1176_, v_i_1178_);
v___x_1198_ = lean_box(0);
v___x_1199_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1193_, v_isLower_1175_, v_a_1197_, v___x_1198_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
lean_dec_ref_known(v___x_1199_, 1);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_unsigned_to_nat(1u);
v___x_1202_ = lean_nat_add(v_snd_1193_, v___x_1201_);
lean_dec(v_snd_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___x_1202_);
lean_ctor_set(v___x_1195_, 0, v___x_1200_);
v___x_1204_ = v___x_1195_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
size_t v___x_1205_; size_t v___x_1206_; 
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_add(v_i_1178_, v___x_1205_);
v_i_1178_ = v___x_1206_;
v_b_1179_ = v___x_1204_;
goto _start;
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_del_object(v___x_1195_);
lean_dec(v_snd_1193_);
v_a_1209_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1199_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1199_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(lean_object* v_isLower_1219_, lean_object* v_as_1220_, lean_object* v_sz_1221_, lean_object* v_i_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v_isLower_boxed_1235_; size_t v_sz_boxed_1236_; size_t v_i_boxed_1237_; lean_object* v_res_1238_; 
v_isLower_boxed_1235_ = lean_unbox(v_isLower_1219_);
v_sz_boxed_1236_ = lean_unbox_usize(v_sz_1221_);
lean_dec(v_sz_1221_);
v_i_boxed_1237_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_res_1238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_1235_, v_as_1220_, v_sz_boxed_1236_, v_i_boxed_1237_, v_b_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v_as_1220_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(uint8_t v_isLower_1239_, lean_object* v_as_1240_, size_t v_sz_1241_, size_t v_i_1242_, lean_object* v_b_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_usize_dec_lt(v_i_1242_, v_sz_1241_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_b_1243_);
return v___x_1256_;
}
else
{
lean_object* v_snd_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1281_; 
v_snd_1257_ = lean_ctor_get(v_b_1243_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_b_1243_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_b_1243_, 0);
lean_dec(v_unused_1282_);
v___x_1259_ = v_b_1243_;
v_isShared_1260_ = v_isSharedCheck_1281_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_snd_1257_);
lean_dec(v_b_1243_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1281_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_a_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_a_1261_ = lean_array_uget_borrowed(v_as_1240_, v_i_1242_);
v___x_1262_ = lean_box(0);
v___x_1263_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_1257_, v_isLower_1239_, v_a_1261_, v___x_1262_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
lean_dec_ref_known(v___x_1263_, 1);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_add(v_snd_1257_, v___x_1265_);
lean_dec(v_snd_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1266_);
lean_ctor_set(v___x_1259_, 0, v___x_1264_);
v___x_1268_ = v___x_1259_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((size_t)1ULL);
v___x_1270_ = lean_usize_add(v_i_1242_, v___x_1269_);
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_1239_, v_as_1240_, v_sz_1241_, v___x_1270_, v___x_1268_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1271_;
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_del_object(v___x_1259_);
lean_dec(v_snd_1257_);
v_a_1273_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1263_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1263_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(lean_object* v_isLower_1283_, lean_object* v_as_1284_, lean_object* v_sz_1285_, lean_object* v_i_1286_, lean_object* v_b_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v_isLower_boxed_1299_; size_t v_sz_boxed_1300_; size_t v_i_boxed_1301_; lean_object* v_res_1302_; 
v_isLower_boxed_1299_ = lean_unbox(v_isLower_1283_);
v_sz_boxed_1300_ = lean_unbox_usize(v_sz_1285_);
lean_dec(v_sz_1285_);
v_i_boxed_1301_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_1299_, v_as_1284_, v_sz_boxed_1300_, v_i_boxed_1301_, v_b_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v_as_1284_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(lean_object* v_init_1303_, uint8_t v_isLower_1304_, lean_object* v_n_1305_, lean_object* v_b_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
if (lean_obj_tag(v_n_1305_) == 0)
{
lean_object* v_cs_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v_cs_1318_ = lean_ctor_get(v_n_1305_, 0);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_b_1306_);
v_sz_1321_ = lean_array_size(v_cs_1318_);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1303_, v_isLower_1304_, v_cs_1318_, v_sz_1321_, v___x_1322_, v___x_1320_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1338_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1338_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1338_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_fst_1328_; 
v_fst_1328_ = lean_ctor_get(v_a_1324_, 0);
if (lean_obj_tag(v_fst_1328_) == 0)
{
lean_object* v_snd_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v_snd_1329_ = lean_ctor_get(v_a_1324_, 1);
lean_inc(v_snd_1329_);
lean_dec(v_a_1324_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_snd_1329_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1330_);
v___x_1332_ = v___x_1326_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_object* v_val_1334_; lean_object* v___x_1336_; 
lean_inc_ref(v_fst_1328_);
lean_dec(v_a_1324_);
v_val_1334_ = lean_ctor_get(v_fst_1328_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v_fst_1328_, 1);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_val_1334_);
v___x_1336_ = v___x_1326_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_val_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
v_a_1339_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1323_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1323_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_vs_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v_vs_1347_ = lean_ctor_get(v_n_1305_, 0);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v_b_1306_);
v_sz_1350_ = lean_array_size(v_vs_1347_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_1304_, v_vs_1347_, v_sz_1350_, v___x_1351_, v___x_1349_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1367_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1367_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1367_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_fst_1357_; 
v_fst_1357_ = lean_ctor_get(v_a_1353_, 0);
if (lean_obj_tag(v_fst_1357_) == 0)
{
lean_object* v_snd_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v_snd_1358_ = lean_ctor_get(v_a_1353_, 1);
lean_inc(v_snd_1358_);
lean_dec(v_a_1353_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_snd_1358_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1359_);
v___x_1361_ = v___x_1355_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
else
{
lean_object* v_val_1363_; lean_object* v___x_1365_; 
lean_inc_ref(v_fst_1357_);
lean_dec(v_a_1353_);
v_val_1363_ = lean_ctor_get(v_fst_1357_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v_fst_1357_, 1);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_val_1363_);
v___x_1365_ = v___x_1355_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_val_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1352_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1352_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(lean_object* v_init_1376_, uint8_t v_isLower_1377_, lean_object* v_as_1378_, size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v_b_1381_);
return v___x_1394_;
}
else
{
lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1429_; 
v_snd_1395_ = lean_ctor_get(v_b_1381_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_b_1381_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v_b_1381_, 0);
lean_dec(v_unused_1430_);
v___x_1397_ = v_b_1381_;
v_isShared_1398_ = v_isSharedCheck_1429_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_dec(v_b_1381_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1429_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_a_1399_; lean_object* v___x_1400_; 
v_a_1399_ = lean_array_uget_borrowed(v_as_1378_, v_i_1380_);
lean_inc(v_snd_1395_);
v___x_1400_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1376_, v_isLower_1377_, v_a_1399_, v_snd_1395_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1420_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1420_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1420_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
if (lean_obj_tag(v_a_1401_) == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_a_1401_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1405_);
v___x_1407_ = v___x_1397_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_snd_1395_);
v___x_1407_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1407_);
v___x_1409_ = v___x_1403_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_del_object(v___x_1403_);
lean_dec(v_snd_1395_);
v_a_1412_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v_a_1401_, 1);
v___x_1413_ = lean_box(0);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v_a_1412_);
lean_ctor_set(v___x_1397_, 0, v___x_1413_);
v___x_1415_ = v___x_1397_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_a_1412_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
size_t v___x_1416_; size_t v___x_1417_; 
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_add(v_i_1380_, v___x_1416_);
v_i_1380_ = v___x_1417_;
v_b_1381_ = v___x_1415_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
v_a_1421_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1400_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1400_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_init_1431_ = _args[0];
lean_object* v_isLower_1432_ = _args[1];
lean_object* v_as_1433_ = _args[2];
lean_object* v_sz_1434_ = _args[3];
lean_object* v_i_1435_ = _args[4];
lean_object* v_b_1436_ = _args[5];
lean_object* v___y_1437_ = _args[6];
lean_object* v___y_1438_ = _args[7];
lean_object* v___y_1439_ = _args[8];
lean_object* v___y_1440_ = _args[9];
lean_object* v___y_1441_ = _args[10];
lean_object* v___y_1442_ = _args[11];
lean_object* v___y_1443_ = _args[12];
lean_object* v___y_1444_ = _args[13];
lean_object* v___y_1445_ = _args[14];
lean_object* v___y_1446_ = _args[15];
lean_object* v___y_1447_ = _args[16];
_start:
{
uint8_t v_isLower_boxed_1448_; size_t v_sz_boxed_1449_; size_t v_i_boxed_1450_; lean_object* v_res_1451_; 
v_isLower_boxed_1448_ = lean_unbox(v_isLower_1432_);
v_sz_boxed_1449_ = lean_unbox_usize(v_sz_1434_);
lean_dec(v_sz_1434_);
v_i_boxed_1450_ = lean_unbox_usize(v_i_1435_);
lean_dec(v_i_1435_);
v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_1431_, v_isLower_boxed_1448_, v_as_1433_, v_sz_boxed_1449_, v_i_boxed_1450_, v_b_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v_as_1433_);
lean_dec(v_init_1431_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4___boxed(lean_object* v_init_1452_, lean_object* v_isLower_1453_, lean_object* v_n_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_isLower_boxed_1467_; lean_object* v_res_1468_; 
v_isLower_boxed_1467_ = lean_unbox(v_isLower_1453_);
v_res_1468_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1452_, v_isLower_boxed_1467_, v_n_1454_, v_b_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v_n_1454_);
lean_dec(v_init_1452_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(uint8_t v_isLower_1469_, lean_object* v_t_1470_, lean_object* v_init_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_root_1483_; lean_object* v_tail_1484_; lean_object* v___x_1485_; 
v_root_1483_ = lean_ctor_get(v_t_1470_, 0);
v_tail_1484_ = lean_ctor_get(v_t_1470_, 1);
lean_inc(v_init_1471_);
v___x_1485_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_1471_, v_isLower_1469_, v_root_1483_, v_init_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v_init_1471_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1522_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1522_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1522_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
if (lean_obj_tag(v_a_1486_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; 
v_a_1490_ = lean_ctor_get(v_a_1486_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v_a_1486_, 1);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v_a_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; size_t v_sz_1497_; size_t v___x_1498_; lean_object* v___x_1499_; 
lean_del_object(v___x_1488_);
v_a_1494_ = lean_ctor_get(v_a_1486_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v_a_1486_, 1);
v___x_1495_ = lean_box(0);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v_a_1494_);
v_sz_1497_ = lean_array_size(v_tail_1484_);
v___x_1498_ = ((size_t)0ULL);
v___x_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_1469_, v_tail_1484_, v_sz_1497_, v___x_1498_, v___x_1496_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1513_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1513_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1513_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_fst_1504_; 
v_fst_1504_ = lean_ctor_get(v_a_1500_, 0);
if (lean_obj_tag(v_fst_1504_) == 0)
{
lean_object* v_snd_1505_; lean_object* v___x_1507_; 
v_snd_1505_ = lean_ctor_get(v_a_1500_, 1);
lean_inc(v_snd_1505_);
lean_dec(v_a_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_snd_1505_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_snd_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
else
{
lean_object* v_val_1509_; lean_object* v___x_1511_; 
lean_inc_ref(v_fst_1504_);
lean_dec(v_a_1500_);
v_val_1509_ = lean_ctor_get(v_fst_1504_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v_fst_1504_, 1);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_val_1509_);
v___x_1511_ = v___x_1502_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_val_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1499_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1499_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v_a_1523_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1485_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1485_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2___boxed(lean_object* v_isLower_1531_, lean_object* v_t_1532_, lean_object* v_init_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v_isLower_boxed_1545_; lean_object* v_res_1546_; 
v_isLower_boxed_1545_ = lean_unbox(v_isLower_1531_);
v_res_1546_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_boxed_1545_, v_t_1532_, v_init_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v_t_1532_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(lean_object* v_css_1547_, uint8_t v_isLower_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_x_1560_; lean_object* v___x_1561_; 
v_x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_1548_, v_css_1547_, v_x_1560_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1569_; 
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v___x_1561_, 0);
lean_dec(v_unused_1570_);
v___x_1563_ = v___x_1561_;
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
else
{
lean_dec(v___x_1561_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = lean_box(0);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
v_a_1571_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1561_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1561_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs___boxed(lean_object* v_css_1579_, lean_object* v_isLower_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
uint8_t v_isLower_boxed_1592_; lean_object* v_res_1593_; 
v_isLower_boxed_1592_ = lean_unbox(v_isLower_1580_);
v_res_1593_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_css_1579_, v_isLower_boxed_1592_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_css_1579_);
return v_res_1593_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1596_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1));
v___x_1597_ = lean_unsigned_to_nat(2u);
v___x_1598_ = lean_unsigned_to_nat(55u);
v___x_1599_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0));
v___x_1600_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1601_ = l_mkPanicMessageWithDecl(v___x_1600_, v___x_1599_, v___x_1598_, v___x_1597_, v___x_1596_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1602_, v_a_1610_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v_lowers_1615_; lean_object* v_vars_1616_; lean_object* v_size_1617_; lean_object* v_size_1618_; uint8_t v___x_1619_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v_lowers_1615_ = lean_ctor_get(v_a_1614_, 7);
lean_inc_ref(v_lowers_1615_);
v_vars_1616_ = lean_ctor_get(v_a_1614_, 0);
lean_inc_ref(v_vars_1616_);
lean_dec(v_a_1614_);
v_size_1617_ = lean_ctor_get(v_lowers_1615_, 2);
v_size_1618_ = lean_ctor_get(v_vars_1616_, 2);
lean_inc(v_size_1618_);
lean_dec_ref(v_vars_1616_);
v___x_1619_ = lean_nat_dec_eq(v_size_1617_, v_size_1618_);
lean_dec(v_size_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec_ref(v_lowers_1615_);
v___x_1620_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2);
v___x_1621_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_1620_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_lowers_1615_, v___x_1619_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
lean_dec_ref(v_lowers_1615_);
return v___x_1622_;
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
v_a_1623_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1613_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1613_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___boxed(lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec(v_a_1631_);
return v_res_1642_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1645_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1));
v___x_1646_ = lean_unsigned_to_nat(2u);
v___x_1647_ = lean_unsigned_to_nat(60u);
v___x_1648_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0));
v___x_1649_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1650_ = l_mkPanicMessageWithDecl(v___x_1649_, v___x_1648_, v___x_1647_, v___x_1646_, v___x_1645_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1651_, v_a_1659_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v_uppers_1664_; lean_object* v_vars_1665_; lean_object* v_size_1666_; lean_object* v_size_1667_; uint8_t v___x_1668_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v_uppers_1664_ = lean_ctor_get(v_a_1663_, 8);
lean_inc_ref(v_uppers_1664_);
v_vars_1665_ = lean_ctor_get(v_a_1663_, 0);
lean_inc_ref(v_vars_1665_);
lean_dec(v_a_1663_);
v_size_1666_ = lean_ctor_get(v_uppers_1664_, 2);
v_size_1667_ = lean_ctor_get(v_vars_1665_, 2);
lean_inc(v_size_1667_);
lean_dec_ref(v_vars_1665_);
v___x_1668_ = lean_nat_dec_eq(v_size_1666_, v_size_1667_);
lean_dec(v_size_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v_uppers_1664_);
v___x_1669_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2);
v___x_1670_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_1669_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1670_;
}
else
{
uint8_t v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = 0;
v___x_1672_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(v_uppers_1664_, v___x_1671_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
lean_dec_ref(v_uppers_1664_);
return v___x_1672_;
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_a_1673_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1662_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1662_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___boxed(lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec(v_a_1681_);
return v_res_1692_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(lean_object* v_msg_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_4904__overap_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0);
v___x_4904__overap_1707_ = lean_panic_fn_borrowed(v___x_1706_, v_msg_1694_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
lean_inc_ref(v___y_1699_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1696_);
lean_inc(v___y_1695_);
v___x_1708_ = lean_apply_11(v___x_4904__overap_1707_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, lean_box(0));
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___boxed(lean_object* v_msg_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v_msg_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec(v___y_1710_);
return v_res_1721_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_nat_to_int(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2));
v___x_1727_ = lean_unsigned_to_nat(6u);
v___x_1728_ = lean_unsigned_to_nat(70u);
v___x_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_1730_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_1731_ = l_mkPanicMessageWithDecl(v___x_1730_, v___x_1729_, v___x_1728_, v___x_1727_, v___x_1726_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1732_, size_t v_sz_1733_, size_t v_i_1734_, lean_object* v_b_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_usize_dec_lt(v_i_1734_, v_sz_1733_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_b_1735_);
return v___x_1748_;
}
else
{
lean_object* v_snd_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1807_; 
v_snd_1749_ = lean_ctor_get(v_b_1735_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_b_1735_);
if (v_isSharedCheck_1807_ == 0)
{
lean_object* v_unused_1808_; 
v_unused_1808_ = lean_ctor_get(v_b_1735_, 0);
lean_dec(v_unused_1808_);
v___x_1751_ = v_b_1735_;
v_isShared_1752_ = v_isSharedCheck_1807_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_snd_1749_);
lean_dec(v_b_1735_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1807_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v_a_1755_; lean_object* v_a_1765_; 
v___x_1753_ = lean_box(0);
v_a_1765_ = lean_array_uget(v_as_1732_, v_i_1734_);
if (lean_obj_tag(v_a_1765_) == 1)
{
lean_object* v_val_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1806_; 
v_val_1766_ = lean_ctor_get(v_a_1765_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1765_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1768_ = v_a_1765_;
v_isShared_1769_ = v_isSharedCheck_1806_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_val_1766_);
lean_dec(v_a_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1806_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_d_1770_; lean_object* v_p_1771_; lean_object* v___x_1772_; 
v_d_1770_ = lean_ctor_get(v_val_1766_, 0);
lean_inc(v_d_1770_);
v_p_1771_ = lean_ctor_get(v_val_1766_, 1);
lean_inc_ref(v_p_1771_);
lean_dec(v_val_1766_);
v___x_1772_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_1771_, v_snd_1749_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec_ref(v_p_1771_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
lean_dec_ref_known(v___x_1772_, 1);
v___x_1773_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1774_ = lean_int_dec_lt(v___x_1773_, v_d_1770_);
lean_dec(v_d_1770_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1776_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1775_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1789_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1789_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1789_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
if (lean_obj_tag(v_a_1777_) == 0)
{
lean_object* v___x_1782_; 
lean_del_object(v___x_1751_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v_a_1777_);
v___x_1782_ = v___x_1768_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_snd_1749_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1783_);
v___x_1785_ = v___x_1779_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1788_; 
lean_del_object(v___x_1779_);
lean_del_object(v___x_1768_);
lean_dec(v_snd_1749_);
v_a_1788_ = lean_ctor_get(v_a_1777_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v_a_1777_, 1);
v_a_1755_ = v_a_1788_;
goto v___jp_1754_;
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_del_object(v___x_1768_);
lean_del_object(v___x_1751_);
lean_dec(v_snd_1749_);
v_a_1790_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1776_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1776_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_del_object(v___x_1768_);
goto v___jp_1762_;
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_d_1770_);
lean_del_object(v___x_1768_);
lean_del_object(v___x_1751_);
lean_dec(v_snd_1749_);
v_a_1798_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1772_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1772_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
else
{
lean_dec(v_a_1765_);
goto v___jp_1762_;
}
v___jp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v_a_1755_);
lean_ctor_set(v___x_1751_, 0, v___x_1753_);
v___x_1757_ = v___x_1751_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_a_1755_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
size_t v___x_1758_; size_t v___x_1759_; 
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_add(v_i_1734_, v___x_1758_);
v_i_1734_ = v___x_1759_;
v_b_1735_ = v___x_1757_;
goto _start;
}
}
v___jp_1762_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_nat_add(v_snd_1749_, v___x_1763_);
lean_dec(v_snd_1749_);
v_a_1755_ = v___x_1764_;
goto v___jp_1754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1809_, lean_object* v_sz_1810_, lean_object* v_i_1811_, lean_object* v_b_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
size_t v_sz_boxed_1824_; size_t v_i_boxed_1825_; lean_object* v_res_1826_; 
v_sz_boxed_1824_ = lean_unbox_usize(v_sz_1810_);
lean_dec(v_sz_1810_);
v_i_boxed_1825_ = lean_unbox_usize(v_i_1811_);
lean_dec(v_i_1811_);
v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1809_, v_sz_boxed_1824_, v_i_boxed_1825_, v_b_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v_as_1809_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(lean_object* v_as_1827_, size_t v_sz_1828_, size_t v_i_1829_, lean_object* v_b_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_lt(v_i_1829_, v_sz_1828_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_b_1830_);
return v___x_1843_;
}
else
{
lean_object* v_snd_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1902_; 
v_snd_1844_ = lean_ctor_get(v_b_1830_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_b_1830_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v_b_1830_, 0);
lean_dec(v_unused_1903_);
v___x_1846_ = v_b_1830_;
v_isShared_1847_ = v_isSharedCheck_1902_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snd_1844_);
lean_dec(v_b_1830_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1902_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v_a_1850_; lean_object* v_a_1860_; 
v___x_1848_ = lean_box(0);
v_a_1860_ = lean_array_uget(v_as_1827_, v_i_1829_);
if (lean_obj_tag(v_a_1860_) == 1)
{
lean_object* v_val_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1901_; 
v_val_1861_ = lean_ctor_get(v_a_1860_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_a_1860_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1863_ = v_a_1860_;
v_isShared_1864_ = v_isSharedCheck_1901_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_val_1861_);
lean_dec(v_a_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1901_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_d_1865_; lean_object* v_p_1866_; lean_object* v___x_1867_; 
v_d_1865_ = lean_ctor_get(v_val_1861_, 0);
lean_inc(v_d_1865_);
v_p_1866_ = lean_ctor_get(v_val_1861_, 1);
lean_inc_ref(v_p_1866_);
lean_dec(v_val_1861_);
v___x_1867_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_1866_, v_snd_1844_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec_ref(v_p_1866_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
lean_dec_ref_known(v___x_1867_, 1);
v___x_1868_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_1869_ = lean_int_dec_lt(v___x_1868_, v_d_1865_);
lean_dec(v_d_1865_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_1871_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_1870_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1884_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1884_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1884_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
if (lean_obj_tag(v_a_1872_) == 0)
{
lean_object* v___x_1877_; 
lean_del_object(v___x_1846_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_a_1872_);
v___x_1877_ = v___x_1863_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_snd_1844_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1878_);
v___x_1880_ = v___x_1874_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_object* v_a_1883_; 
lean_del_object(v___x_1874_);
lean_del_object(v___x_1863_);
lean_dec(v_snd_1844_);
v_a_1883_ = lean_ctor_get(v_a_1872_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v_a_1872_, 1);
v_a_1850_ = v_a_1883_;
goto v___jp_1849_;
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_del_object(v___x_1863_);
lean_del_object(v___x_1846_);
lean_dec(v_snd_1844_);
v_a_1885_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1871_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1871_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_del_object(v___x_1863_);
goto v___jp_1857_;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_d_1865_);
lean_del_object(v___x_1863_);
lean_del_object(v___x_1846_);
lean_dec(v_snd_1844_);
v_a_1893_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1867_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1867_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
lean_dec(v_a_1860_);
goto v___jp_1857_;
}
v___jp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v_a_1850_);
lean_ctor_set(v___x_1846_, 0, v___x_1848_);
v___x_1852_ = v___x_1846_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_a_1850_);
v___x_1852_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_add(v_i_1829_, v___x_1853_);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_1827_, v_sz_1828_, v___x_1854_, v___x_1852_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1855_;
}
}
v___jp_1857_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = lean_nat_add(v_snd_1844_, v___x_1858_);
lean_dec(v_snd_1844_);
v_a_1850_ = v___x_1859_;
goto v___jp_1849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1904_, lean_object* v_sz_1905_, lean_object* v_i_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
size_t v_sz_boxed_1919_; size_t v_i_boxed_1920_; lean_object* v_res_1921_; 
v_sz_boxed_1919_ = lean_unbox_usize(v_sz_1905_);
lean_dec(v_sz_1905_);
v_i_boxed_1920_ = lean_unbox_usize(v_i_1906_);
lean_dec(v_i_1906_);
v_res_1921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_as_1904_, v_sz_boxed_1919_, v_i_boxed_1920_, v_b_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v_as_1904_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(lean_object* v_init_1922_, lean_object* v_n_1923_, lean_object* v_b_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
if (lean_obj_tag(v_n_1923_) == 0)
{
lean_object* v_cs_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; size_t v_sz_1939_; size_t v___x_1940_; lean_object* v___x_1941_; 
v_cs_1936_ = lean_ctor_get(v_n_1923_, 0);
v___x_1937_ = lean_box(0);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v_b_1924_);
v_sz_1939_ = lean_array_size(v_cs_1936_);
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_1922_, v_cs_1936_, v_sz_1939_, v___x_1940_, v___x_1938_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1956_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1956_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1956_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_fst_1946_; 
v_fst_1946_ = lean_ctor_get(v_a_1942_, 0);
if (lean_obj_tag(v_fst_1946_) == 0)
{
lean_object* v_snd_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v_snd_1947_ = lean_ctor_get(v_a_1942_, 1);
lean_inc(v_snd_1947_);
lean_dec(v_a_1942_);
v___x_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1948_, 0, v_snd_1947_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1948_);
v___x_1950_ = v___x_1944_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
else
{
lean_object* v_val_1952_; lean_object* v___x_1954_; 
lean_inc_ref(v_fst_1946_);
lean_dec(v_a_1942_);
v_val_1952_ = lean_ctor_get(v_fst_1946_, 0);
lean_inc(v_val_1952_);
lean_dec_ref_known(v_fst_1946_, 1);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v_val_1952_);
v___x_1954_ = v___x_1944_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_val_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
v_a_1957_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1941_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1941_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_vs_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; size_t v_sz_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v_vs_1965_ = lean_ctor_get(v_n_1923_, 0);
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
lean_ctor_set(v___x_1967_, 1, v_b_1924_);
v_sz_1968_ = lean_array_size(v_vs_1965_);
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_vs_1965_, v_sz_1968_, v___x_1969_, v___x_1967_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1985_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_fst_1975_; 
v_fst_1975_ = lean_ctor_get(v_a_1971_, 0);
if (lean_obj_tag(v_fst_1975_) == 0)
{
lean_object* v_snd_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v_snd_1976_ = lean_ctor_get(v_a_1971_, 1);
lean_inc(v_snd_1976_);
lean_dec(v_a_1971_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_snd_1976_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1977_);
v___x_1979_ = v___x_1973_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
else
{
lean_object* v_val_1981_; lean_object* v___x_1983_; 
lean_inc_ref(v_fst_1975_);
lean_dec(v_a_1971_);
v_val_1981_ = lean_ctor_get(v_fst_1975_, 0);
lean_inc(v_val_1981_);
lean_dec_ref_known(v_fst_1975_, 1);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v_val_1981_);
v___x_1983_ = v___x_1973_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_val_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
v_a_1986_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1970_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1970_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(lean_object* v_init_1994_, lean_object* v_as_1995_, size_t v_sz_1996_, size_t v_i_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_usize_dec_lt(v_i_1997_, v_sz_1996_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v_b_1998_);
return v___x_2011_;
}
else
{
lean_object* v_snd_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2046_; 
v_snd_2012_ = lean_ctor_get(v_b_1998_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_b_1998_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_b_1998_, 0);
lean_dec(v_unused_2047_);
v___x_2014_ = v_b_1998_;
v_isShared_2015_ = v_isSharedCheck_2046_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_snd_2012_);
lean_dec(v_b_1998_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2046_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_a_2016_; lean_object* v___x_2017_; 
v_a_2016_ = lean_array_uget_borrowed(v_as_1995_, v_i_1997_);
lean_inc(v_snd_2012_);
v___x_2017_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_1994_, v_a_2016_, v_snd_2012_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2037_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2037_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2037_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
if (lean_obj_tag(v_a_2018_) == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_a_2018_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2022_);
v___x_2024_ = v___x_2014_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_snd_2012_);
v___x_2024_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2024_);
v___x_2026_ = v___x_2020_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_del_object(v___x_2020_);
lean_dec(v_snd_2012_);
v_a_2029_ = lean_ctor_get(v_a_2018_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v_a_2018_, 1);
v___x_2030_ = lean_box(0);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v_a_2029_);
lean_ctor_set(v___x_2014_, 0, v___x_2030_);
v___x_2032_ = v___x_2014_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_a_2029_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
size_t v___x_2033_; size_t v___x_2034_; 
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_1997_, v___x_2033_);
v_i_1997_ = v___x_2034_;
v_b_1998_ = v___x_2032_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_del_object(v___x_2014_);
lean_dec(v_snd_2012_);
v_a_2038_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2017_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2017_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2___boxed(lean_object* v_init_2048_, lean_object* v_as_2049_, lean_object* v_sz_2050_, lean_object* v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
size_t v_sz_boxed_2064_; size_t v_i_boxed_2065_; lean_object* v_res_2066_; 
v_sz_boxed_2064_ = lean_unbox_usize(v_sz_2050_);
lean_dec(v_sz_2050_);
v_i_boxed_2065_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_res_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_2048_, v_as_2049_, v_sz_boxed_2064_, v_i_boxed_2065_, v_b_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v_as_2049_);
lean_dec(v_init_2048_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1___boxed(lean_object* v_init_2067_, lean_object* v_n_2068_, lean_object* v_b_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2067_, v_n_2068_, v_b_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v_n_2068_);
lean_dec(v_init_2067_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(lean_object* v_as_2082_, size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_lt(v_i_2084_, v_sz_2083_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_b_2085_);
return v___x_2098_;
}
else
{
lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2158_; 
v_snd_2099_ = lean_ctor_get(v_b_2085_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v_b_2085_, 0);
lean_dec(v_unused_2159_);
v___x_2101_ = v_b_2085_;
v_isShared_2102_ = v_isSharedCheck_2158_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_dec(v_b_2085_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2158_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v_a_2105_; lean_object* v_a_2115_; 
v___x_2103_ = lean_box(0);
v_a_2115_ = lean_array_uget(v_as_2082_, v_i_2084_);
if (lean_obj_tag(v_a_2115_) == 1)
{
lean_object* v_val_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2157_; 
v_val_2116_ = lean_ctor_get(v_a_2115_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_a_2115_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2118_ = v_a_2115_;
v_isShared_2119_ = v_isSharedCheck_2157_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_val_2116_);
lean_dec(v_a_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2157_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_d_2120_; lean_object* v_p_2121_; lean_object* v___x_2122_; 
v_d_2120_ = lean_ctor_get(v_val_2116_, 0);
lean_inc(v_d_2120_);
v_p_2121_ = lean_ctor_get(v_val_2116_, 1);
lean_inc_ref(v_p_2121_);
lean_dec(v_val_2116_);
v___x_2122_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_2121_, v_snd_2099_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec_ref(v_p_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
lean_dec_ref_known(v___x_2122_, 1);
v___x_2123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2124_ = lean_int_dec_lt(v___x_2123_, v_d_2120_);
lean_dec(v_d_2120_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2126_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2125_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2140_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
if (lean_obj_tag(v_a_2127_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; 
lean_del_object(v___x_2101_);
v_a_2131_ = lean_ctor_get(v_a_2127_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v_a_2127_, 1);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v_a_2131_);
v___x_2133_ = v___x_2118_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2131_);
v___x_2133_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v_snd_2099_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2134_);
v___x_2136_ = v___x_2129_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
lean_object* v_a_2139_; 
lean_del_object(v___x_2129_);
lean_del_object(v___x_2118_);
lean_dec(v_snd_2099_);
v_a_2139_ = lean_ctor_get(v_a_2127_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v_a_2127_, 1);
v_a_2105_ = v_a_2139_;
goto v___jp_2104_;
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_del_object(v___x_2118_);
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
v_a_2141_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2126_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2126_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_del_object(v___x_2118_);
goto v___jp_2112_;
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_d_2120_);
lean_del_object(v___x_2118_);
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
v_a_2149_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2122_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2122_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
else
{
lean_dec(v_a_2115_);
goto v___jp_2112_;
}
v___jp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v_a_2105_);
lean_ctor_set(v___x_2101_, 0, v___x_2103_);
v___x_2107_ = v___x_2101_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_a_2105_);
v___x_2107_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
size_t v___x_2108_; size_t v___x_2109_; 
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_add(v_i_2084_, v___x_2108_);
v_i_2084_ = v___x_2109_;
v_b_2085_ = v___x_2107_;
goto _start;
}
}
v___jp_2112_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_unsigned_to_nat(1u);
v___x_2114_ = lean_nat_add(v_snd_2099_, v___x_2113_);
lean_dec(v_snd_2099_);
v_a_2105_ = v___x_2114_;
goto v___jp_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2160_, lean_object* v_sz_2161_, lean_object* v_i_2162_, lean_object* v_b_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
size_t v_sz_boxed_2175_; size_t v_i_boxed_2176_; lean_object* v_res_2177_; 
v_sz_boxed_2175_ = lean_unbox_usize(v_sz_2161_);
lean_dec(v_sz_2161_);
v_i_boxed_2176_ = lean_unbox_usize(v_i_2162_);
lean_dec(v_i_2162_);
v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2160_, v_sz_boxed_2175_, v_i_boxed_2176_, v_b_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v_as_2160_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(lean_object* v_as_2178_, size_t v_sz_2179_, size_t v_i_2180_, lean_object* v_b_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
uint8_t v___x_2193_; 
v___x_2193_ = lean_usize_dec_lt(v_i_2180_, v_sz_2179_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v_b_2181_);
return v___x_2194_;
}
else
{
lean_object* v_snd_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2254_; 
v_snd_2195_ = lean_ctor_get(v_b_2181_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_b_2181_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v_b_2181_, 0);
lean_dec(v_unused_2255_);
v___x_2197_ = v_b_2181_;
v_isShared_2198_ = v_isSharedCheck_2254_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_snd_2195_);
lean_dec(v_b_2181_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2254_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v_a_2201_; lean_object* v_a_2211_; 
v___x_2199_ = lean_box(0);
v_a_2211_ = lean_array_uget(v_as_2178_, v_i_2180_);
if (lean_obj_tag(v_a_2211_) == 1)
{
lean_object* v_val_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2253_; 
v_val_2212_ = lean_ctor_get(v_a_2211_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_a_2211_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2214_ = v_a_2211_;
v_isShared_2215_ = v_isSharedCheck_2253_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_val_2212_);
lean_dec(v_a_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2253_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_d_2216_; lean_object* v_p_2217_; lean_object* v___x_2218_; 
v_d_2216_ = lean_ctor_get(v_val_2212_, 0);
lean_inc(v_d_2216_);
v_p_2217_ = lean_ctor_get(v_val_2212_, 1);
lean_inc_ref(v_p_2217_);
lean_dec(v_val_2212_);
v___x_2218_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_2217_, v_snd_2195_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec_ref(v_p_2217_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v___x_2219_; uint8_t v___x_2220_; 
lean_dec_ref_known(v___x_2218_, 1);
v___x_2219_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
v___x_2220_ = lean_int_dec_lt(v___x_2219_, v_d_2216_);
lean_dec(v_d_2216_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
v___x_2222_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2221_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2236_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2236_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2236_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
if (lean_obj_tag(v_a_2223_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; 
lean_del_object(v___x_2197_);
v_a_2227_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v_a_2223_, 1);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v_a_2227_);
v___x_2229_ = v___x_2214_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2227_);
v___x_2229_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v_snd_2195_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2230_);
v___x_2232_ = v___x_2225_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
else
{
lean_object* v_a_2235_; 
lean_del_object(v___x_2225_);
lean_del_object(v___x_2214_);
lean_dec(v_snd_2195_);
v_a_2235_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v_a_2223_, 1);
v_a_2201_ = v_a_2235_;
goto v___jp_2200_;
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_del_object(v___x_2214_);
lean_del_object(v___x_2197_);
lean_dec(v_snd_2195_);
v_a_2237_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2222_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2222_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_del_object(v___x_2214_);
goto v___jp_2208_;
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_d_2216_);
lean_del_object(v___x_2214_);
lean_del_object(v___x_2197_);
lean_dec(v_snd_2195_);
v_a_2245_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2218_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2218_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
lean_dec(v_a_2211_);
goto v___jp_2208_;
}
v___jp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 1, v_a_2201_);
lean_ctor_set(v___x_2197_, 0, v___x_2199_);
v___x_2203_ = v___x_2197_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_a_2201_);
v___x_2203_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
size_t v___x_2204_; size_t v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = ((size_t)1ULL);
v___x_2205_ = lean_usize_add(v_i_2180_, v___x_2204_);
v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_2178_, v_sz_2179_, v___x_2205_, v___x_2203_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
return v___x_2206_;
}
}
v___jp_2208_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_unsigned_to_nat(1u);
v___x_2210_ = lean_nat_add(v_snd_2195_, v___x_2209_);
lean_dec(v_snd_2195_);
v_a_2201_ = v___x_2210_;
goto v___jp_2200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2___boxed(lean_object* v_as_2256_, lean_object* v_sz_2257_, lean_object* v_i_2258_, lean_object* v_b_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2257_);
lean_dec(v_sz_2257_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_as_2256_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v_as_2256_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(lean_object* v_t_2274_, lean_object* v_init_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_root_2287_; lean_object* v_tail_2288_; lean_object* v___x_2289_; 
v_root_2287_ = lean_ctor_get(v_t_2274_, 0);
v_tail_2288_ = lean_ctor_get(v_t_2274_, 1);
lean_inc(v_init_2275_);
v___x_2289_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_2275_, v_root_2287_, v_init_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v_init_2275_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2326_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2326_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2326_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
if (lean_obj_tag(v_a_2290_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; 
v_a_2294_ = lean_ctor_get(v_a_2290_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v_a_2290_, 1);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v_a_2294_);
v___x_2296_ = v___x_2292_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
lean_del_object(v___x_2292_);
v_a_2298_ = lean_ctor_get(v_a_2290_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v_a_2290_, 1);
v___x_2299_ = lean_box(0);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v_a_2298_);
v_sz_2301_ = lean_array_size(v_tail_2288_);
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_tail_2288_, v_sz_2301_, v___x_2302_, v___x_2300_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2317_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2317_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2317_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_fst_2308_; 
v_fst_2308_ = lean_ctor_get(v_a_2304_, 0);
if (lean_obj_tag(v_fst_2308_) == 0)
{
lean_object* v_snd_2309_; lean_object* v___x_2311_; 
v_snd_2309_ = lean_ctor_get(v_a_2304_, 1);
lean_inc(v_snd_2309_);
lean_dec(v_a_2304_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v_snd_2309_);
v___x_2311_ = v___x_2306_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_snd_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
else
{
lean_object* v_val_2313_; lean_object* v___x_2315_; 
lean_inc_ref(v_fst_2308_);
lean_dec(v_a_2304_);
v_val_2313_ = lean_ctor_get(v_fst_2308_, 0);
lean_inc(v_val_2313_);
lean_dec_ref_known(v_fst_2308_, 1);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v_val_2313_);
v___x_2315_ = v___x_2306_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_val_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
v_a_2318_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2303_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2303_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
v_a_2327_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2289_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2289_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1___boxed(lean_object* v_t_2335_, lean_object* v_init_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_t_2335_, v_init_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v_t_2335_);
return v_res_2348_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2350_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0));
v___x_2351_ = lean_unsigned_to_nat(2u);
v___x_2352_ = lean_unsigned_to_nat(65u);
v___x_2353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_2354_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2355_ = l_mkPanicMessageWithDecl(v___x_2354_, v___x_2353_, v___x_2352_, v___x_2351_, v___x_2350_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2356_, v_a_2364_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v_vars_2369_; lean_object* v_dvds_2370_; lean_object* v_size_2371_; lean_object* v_size_2372_; uint8_t v___x_2373_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v_vars_2369_ = lean_ctor_get(v_a_2368_, 0);
lean_inc_ref(v_vars_2369_);
v_dvds_2370_ = lean_ctor_get(v_a_2368_, 6);
lean_inc_ref(v_dvds_2370_);
lean_dec(v_a_2368_);
v_size_2371_ = lean_ctor_get(v_vars_2369_, 2);
lean_inc(v_size_2371_);
lean_dec_ref(v_vars_2369_);
v_size_2372_ = lean_ctor_get(v_dvds_2370_, 2);
v___x_2373_ = lean_nat_dec_eq(v_size_2371_, v_size_2372_);
lean_dec(v_size_2371_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec_ref(v_dvds_2370_);
v___x_2374_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1);
v___x_2375_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2374_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_dvds_2370_, v___x_2376_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
lean_dec_ref(v_dvds_2370_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2385_; 
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v___x_2377_, 0);
lean_dec(v_unused_2386_);
v___x_2379_ = v___x_2377_;
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
else
{
lean_dec(v___x_2377_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2381_ = lean_box(0);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2381_);
v___x_2383_ = v___x_2379_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_a_2387_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2377_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2377_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
v_a_2395_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2367_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2367_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___boxed(lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec(v_a_2403_);
return v_res_2414_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2416_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkCnstrOf___closed__3));
v___x_2417_ = lean_unsigned_to_nat(6u);
v___x_2418_ = lean_unsigned_to_nat(81u);
v___x_2419_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2420_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2421_ = l_mkPanicMessageWithDecl(v___x_2420_, v___x_2419_, v___x_2418_, v___x_2417_, v___x_2416_);
return v___x_2421_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2423_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2));
v___x_2424_ = lean_unsigned_to_nat(6u);
v___x_2425_ = lean_unsigned_to_nat(79u);
v___x_2426_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2427_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2428_ = l_mkPanicMessageWithDecl(v___x_2427_, v___x_2426_, v___x_2425_, v___x_2424_, v___x_2423_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(lean_object* v_vars_2429_, lean_object* v_x_2430_, lean_object* v_____s_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_fst_2448_; lean_object* v_snd_2449_; lean_object* v_size_2450_; uint8_t v___x_2451_; 
v_fst_2448_ = lean_ctor_get(v_x_2430_, 0);
v_snd_2449_ = lean_ctor_get(v_x_2430_, 1);
v_size_2450_ = lean_ctor_get(v_vars_2429_, 2);
v___x_2451_ = lean_nat_dec_lt(v_snd_2449_, v_size_2450_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1);
v___x_2453_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2452_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_dec_ref_known(v___x_2453_, 1);
goto v___jp_2443_;
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2462_ = l_Lean_instInhabitedExpr;
v___x_2463_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2462_, v_vars_2429_, v_snd_2449_);
v___x_2464_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2448_, v___x_2463_);
lean_dec(v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3);
v___x_2466_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_2465_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2466_;
}
else
{
goto v___jp_2443_;
}
}
v___jp_2443_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_nat_add(v_____s_2431_, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(lean_object* v_vars_2467_, lean_object* v_x_2468_, lean_object* v_____s_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(v_vars_2467_, v_x_2468_, v_____s_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec(v_____s_2469_);
lean_dec_ref(v_x_2468_);
lean_dec_ref(v_vars_2467_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2482_, lean_object* v_keys_2483_, lean_object* v_vals_2484_, lean_object* v_i_2485_, lean_object* v_acc_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = lean_array_get_size(v_keys_2483_);
v___x_2499_ = lean_nat_dec_lt(v_i_2485_, v___x_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec(v_i_2485_);
lean_dec_ref(v_f_2482_);
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_acc_2486_);
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
else
{
lean_object* v_k_2502_; lean_object* v_v_2503_; lean_object* v___x_2504_; 
v_k_2502_ = lean_array_fget_borrowed(v_keys_2483_, v_i_2485_);
v_v_2503_ = lean_array_fget_borrowed(v_vals_2484_, v_i_2485_);
lean_inc_ref(v_f_2482_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
lean_inc(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc(v_v_2503_);
lean_inc(v_k_2502_);
v___x_2504_ = lean_apply_14(v_f_2482_, v_acc_2486_, v_k_2502_, v_v_2503_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, lean_box(0));
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
if (lean_obj_tag(v_a_2505_) == 0)
{
lean_dec_ref_known(v_a_2505_, 1);
lean_dec(v_i_2485_);
lean_dec_ref(v_f_2482_);
return v___x_2504_;
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_dec_ref_known(v___x_2504_, 1);
v_a_2506_ = lean_ctor_get(v_a_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v_a_2505_, 1);
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_nat_add(v_i_2485_, v___x_2507_);
lean_dec(v_i_2485_);
v_i_2485_ = v___x_2508_;
v_acc_2486_ = v_a_2506_;
goto _start;
}
}
else
{
lean_dec(v_i_2485_);
lean_dec_ref(v_f_2482_);
return v___x_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2510_, lean_object* v_keys_2511_, lean_object* v_vals_2512_, lean_object* v_i_2513_, lean_object* v_acc_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2510_, v_keys_2511_, v_vals_2512_, v_i_2513_, v_acc_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v_vals_2512_);
lean_dec_ref(v_keys_2511_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
if (lean_obj_tag(v_x_2528_) == 0)
{
lean_object* v_es_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2563_; 
v_es_2541_ = lean_ctor_get(v_x_2528_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_x_2528_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2543_ = v_x_2528_;
v_isShared_2544_ = v_isSharedCheck_2563_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_es_2541_);
lean_dec(v_x_2528_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2563_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_array_get_size(v_es_2541_);
v___x_2547_ = lean_nat_dec_lt(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2549_; 
lean_dec_ref(v_es_2541_);
lean_dec_ref(v_f_2527_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 1);
lean_ctor_set(v___x_2543_, 0, v_x_2529_);
v___x_2549_ = v___x_2543_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_x_2529_);
v___x_2549_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
else
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_nat_dec_le(v___x_2546_, v___x_2546_);
if (v___x_2552_ == 0)
{
if (v___x_2547_ == 0)
{
lean_object* v___x_2554_; 
lean_dec_ref(v_es_2541_);
lean_dec_ref(v_f_2527_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 1);
lean_ctor_set(v___x_2543_, 0, v_x_2529_);
v___x_2554_ = v___x_2543_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_x_2529_);
v___x_2554_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
else
{
size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
lean_del_object(v___x_2543_);
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2546_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2527_, v_es_2541_, v___x_2557_, v___x_2558_, v_x_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v_es_2541_);
return v___x_2559_;
}
}
else
{
size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
lean_del_object(v___x_2543_);
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = lean_usize_of_nat(v___x_2546_);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2527_, v_es_2541_, v___x_2560_, v___x_2561_, v_x_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v_es_2541_);
return v___x_2562_;
}
}
}
}
else
{
lean_object* v_ks_2564_; lean_object* v_vs_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_ks_2564_ = lean_ctor_get(v_x_2528_, 0);
lean_inc_ref(v_ks_2564_);
v_vs_2565_ = lean_ctor_get(v_x_2528_, 1);
lean_inc_ref(v_vs_2565_);
lean_dec_ref_known(v_x_2528_, 2);
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2527_, v_ks_2564_, v_vs_2565_, v___x_2566_, v_x_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v_vs_2565_);
lean_dec_ref(v_ks_2564_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2568_, lean_object* v_as_2569_, size_t v_i_2570_, size_t v_stop_2571_, lean_object* v_b_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_a_2585_; lean_object* v___y_2590_; uint8_t v___x_2593_; 
v___x_2593_ = lean_usize_dec_eq(v_i_2570_, v_stop_2571_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_array_uget_borrowed(v_as_2569_, v_i_2570_);
switch(lean_obj_tag(v___x_2594_))
{
case 0:
{
lean_object* v_key_2595_; lean_object* v_val_2596_; lean_object* v___x_2597_; 
v_key_2595_ = lean_ctor_get(v___x_2594_, 0);
v_val_2596_ = lean_ctor_get(v___x_2594_, 1);
lean_inc_ref(v_f_2568_);
lean_inc(v___y_2582_);
lean_inc_ref(v___y_2581_);
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc(v___y_2573_);
lean_inc(v_val_2596_);
lean_inc(v_key_2595_);
v___x_2597_ = lean_apply_14(v_f_2568_, v_b_2572_, v_key_2595_, v_val_2596_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, lean_box(0));
v___y_2590_ = v___x_2597_;
goto v___jp_2589_;
}
case 1:
{
lean_object* v_node_2598_; lean_object* v___x_2599_; 
v_node_2598_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_node_2598_);
lean_inc_ref(v_f_2568_);
v___x_2599_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2568_, v_node_2598_, v_b_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
v___y_2590_ = v___x_2599_;
goto v___jp_2589_;
}
default: 
{
v_a_2585_ = v_b_2572_;
goto v___jp_2584_;
}
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v_f_2568_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v_b_2572_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
v___jp_2584_:
{
size_t v___x_2586_; size_t v___x_2587_; 
v___x_2586_ = ((size_t)1ULL);
v___x_2587_ = lean_usize_add(v_i_2570_, v___x_2586_);
v_i_2570_ = v___x_2587_;
v_b_2572_ = v_a_2585_;
goto _start;
}
v___jp_2589_:
{
if (lean_obj_tag(v___y_2590_) == 0)
{
lean_object* v_a_2591_; 
v_a_2591_ = lean_ctor_get(v___y_2590_, 0);
if (lean_obj_tag(v_a_2591_) == 0)
{
lean_dec_ref(v_f_2568_);
return v___y_2590_;
}
else
{
lean_object* v_a_2592_; 
lean_inc_ref(v_a_2591_);
lean_dec_ref_known(v___y_2590_, 1);
v_a_2592_ = lean_ctor_get(v_a_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v_a_2591_, 1);
v_a_2585_ = v_a_2592_;
goto v___jp_2584_;
}
}
else
{
lean_dec_ref(v_f_2568_);
return v___y_2590_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2602_, lean_object* v_as_2603_, lean_object* v_i_2604_, lean_object* v_stop_2605_, lean_object* v_b_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
size_t v_i_boxed_2618_; size_t v_stop_boxed_2619_; lean_object* v_res_2620_; 
v_i_boxed_2618_ = lean_unbox_usize(v_i_2604_);
lean_dec(v_i_2604_);
v_stop_boxed_2619_ = lean_unbox_usize(v_stop_2605_);
lean_dec(v_stop_2605_);
v_res_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2602_, v_as_2603_, v_i_boxed_2618_, v_stop_boxed_2619_, v_b_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v_as_2603_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2621_, v_x_2622_, v_x_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec(v___y_2624_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(lean_object* v_f_2636_, lean_object* v_s_2637_, lean_object* v_a_2638_, lean_object* v_b_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2651_, 0, v_a_2638_);
lean_ctor_set(v___x_2651_, 1, v_b_2639_);
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
lean_inc(v___y_2645_);
lean_inc_ref(v___y_2644_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
lean_inc(v___y_2641_);
lean_inc(v___y_2640_);
v___x_2652_ = lean_apply_13(v_f_2636_, v___x_2651_, v_s_2637_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, lean_box(0));
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2679_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2679_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2679_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
if (lean_obj_tag(v_a_2653_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2667_; 
v_a_2657_ = lean_ctor_get(v_a_2653_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2659_ = v_a_2653_;
v_isShared_2660_ = v_isSharedCheck_2667_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v_a_2653_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2667_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2664_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2662_);
v___x_2664_ = v___x_2655_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2678_; 
v_a_2668_ = lean_ctor_get(v_a_2653_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2670_ = v_a_2653_;
v_isShared_2671_ = v_isSharedCheck_2678_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v_a_2653_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2678_;
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
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2675_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2673_);
v___x_2675_ = v___x_2655_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
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
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_a_2680_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2652_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2652_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed(lean_object* v_f_2688_, lean_object* v_s_2689_, lean_object* v_a_2690_, lean_object* v_b_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(v_f_2688_, v_s_2689_, v_a_2690_, v_b_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec(v___y_2692_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(lean_object* v_map_2704_, lean_object* v_init_2705_, lean_object* v_f_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___f_2718_; lean_object* v___x_2719_; 
v___f_2718_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed), 15, 1);
lean_closure_set(v___f_2718_, 0, v_f_2706_);
lean_inc_ref(v_map_2704_);
v___x_2719_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v___f_2718_, v_map_2704_, v_init_2705_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2728_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_a_2724_; lean_object* v___x_2726_; 
v_a_2724_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_a_2724_);
lean_dec(v_a_2720_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v_a_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
v_a_2729_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2719_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2719_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___boxed(lean_object* v_map_2737_, lean_object* v_init_2738_, lean_object* v_f_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2737_, v_init_2738_, v_f_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
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
lean_dec_ref(v_map_2737_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2753_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0));
v___x_2754_ = lean_unsigned_to_nat(2u);
v___x_2755_ = lean_unsigned_to_nat(83u);
v___x_2756_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0));
v___x_2757_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_2758_ = l_mkPanicMessageWithDecl(v___x_2757_, v___x_2756_, v___x_2755_, v___x_2754_, v___x_2753_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars(lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2759_, v_a_2767_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v_vars_2772_; lean_object* v_varMap_2773_; lean_object* v___f_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v_vars_2772_ = lean_ctor_get(v_a_2771_, 0);
lean_inc_ref_n(v_vars_2772_, 2);
v_varMap_2773_ = lean_ctor_get(v_a_2771_, 1);
lean_inc_ref(v_varMap_2773_);
lean_dec(v_a_2771_);
v___f_2774_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2774_, 0, v_vars_2772_);
v___x_2775_ = lean_unsigned_to_nat(0u);
v___x_2776_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_varMap_2773_, v___x_2775_, v___f_2774_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec_ref(v_varMap_2773_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2789_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2789_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2789_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_size_2781_; uint8_t v___x_2782_; 
v_size_2781_ = lean_ctor_get(v_vars_2772_, 2);
lean_inc(v_size_2781_);
lean_dec_ref(v_vars_2772_);
v___x_2782_ = lean_nat_dec_eq(v_size_2781_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec(v_size_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_del_object(v___x_2779_);
v___x_2783_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1);
v___x_2784_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_2783_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
return v___x_2784_;
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_box(0);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2785_);
v___x_2787_ = v___x_2779_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref(v_vars_2772_);
v_a_2790_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2776_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2776_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
v_a_2798_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2770_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2770_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkVars___boxed(lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec(v_a_2806_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(lean_object* v_00_u03c3_2818_, lean_object* v_00_u03b2_2819_, lean_object* v_map_2820_, lean_object* v_init_2821_, lean_object* v_f_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_2820_, v_init_2821_, v_f_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___boxed(lean_object* v_00_u03c3_2835_, lean_object* v_00_u03b2_2836_, lean_object* v_map_2837_, lean_object* v_init_2838_, lean_object* v_f_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(v_00_u03c3_2835_, v_00_u03b2_2836_, v_map_2837_, v_init_2838_, v_f_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v_map_2837_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(lean_object* v_map_2852_, lean_object* v_f_2853_, lean_object* v_init_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2853_, v_map_2852_, v_init_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg___boxed(lean_object* v_map_2867_, lean_object* v_f_2868_, lean_object* v_init_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(v_map_2867_, v_f_2868_, v_init_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec(v___y_2870_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(lean_object* v_00_u03c3_2882_, lean_object* v_00_u03c3_2883_, lean_object* v_00_u03b2_2884_, lean_object* v_map_2885_, lean_object* v_f_2886_, lean_object* v_init_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2886_, v_map_2885_, v_init_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_2900_ = _args[0];
lean_object* v_00_u03c3_2901_ = _args[1];
lean_object* v_00_u03b2_2902_ = _args[2];
lean_object* v_map_2903_ = _args[3];
lean_object* v_f_2904_ = _args[4];
lean_object* v_init_2905_ = _args[5];
lean_object* v___y_2906_ = _args[6];
lean_object* v___y_2907_ = _args[7];
lean_object* v___y_2908_ = _args[8];
lean_object* v___y_2909_ = _args[9];
lean_object* v___y_2910_ = _args[10];
lean_object* v___y_2911_ = _args[11];
lean_object* v___y_2912_ = _args[12];
lean_object* v___y_2913_ = _args[13];
lean_object* v___y_2914_ = _args[14];
lean_object* v___y_2915_ = _args[15];
lean_object* v___y_2916_ = _args[16];
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(v_00_u03c3_2900_, v_00_u03c3_2901_, v_00_u03b2_2902_, v_map_2903_, v_f_2904_, v_init_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec(v___y_2906_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2918_, lean_object* v_00_u03c3_2919_, lean_object* v_00_u03b1_2920_, lean_object* v_00_u03b2_2921_, lean_object* v_f_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_2922_, v_x_2923_, v_x_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03c3_2937_ = _args[0];
lean_object* v_00_u03c3_2938_ = _args[1];
lean_object* v_00_u03b1_2939_ = _args[2];
lean_object* v_00_u03b2_2940_ = _args[3];
lean_object* v_f_2941_ = _args[4];
lean_object* v_x_2942_ = _args[5];
lean_object* v_x_2943_ = _args[6];
lean_object* v___y_2944_ = _args[7];
lean_object* v___y_2945_ = _args[8];
lean_object* v___y_2946_ = _args[9];
lean_object* v___y_2947_ = _args[10];
lean_object* v___y_2948_ = _args[11];
lean_object* v___y_2949_ = _args[12];
lean_object* v___y_2950_ = _args[13];
lean_object* v___y_2951_ = _args[14];
lean_object* v___y_2952_ = _args[15];
lean_object* v___y_2953_ = _args[16];
lean_object* v___y_2954_ = _args[17];
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(v_00_u03c3_2937_, v_00_u03c3_2938_, v_00_u03b1_2939_, v_00_u03b2_2940_, v_f_2941_, v_x_2942_, v_x_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2944_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2956_, lean_object* v_00_u03b2_2957_, lean_object* v_00_u03c3_2958_, lean_object* v_00_u03c3_2959_, lean_object* v_f_2960_, lean_object* v_as_2961_, size_t v_i_2962_, size_t v_stop_2963_, lean_object* v_b_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2960_, v_as_2961_, v_i_2962_, v_stop_2963_, v_b_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03b1_2977_ = _args[0];
lean_object* v_00_u03b2_2978_ = _args[1];
lean_object* v_00_u03c3_2979_ = _args[2];
lean_object* v_00_u03c3_2980_ = _args[3];
lean_object* v_f_2981_ = _args[4];
lean_object* v_as_2982_ = _args[5];
lean_object* v_i_2983_ = _args[6];
lean_object* v_stop_2984_ = _args[7];
lean_object* v_b_2985_ = _args[8];
lean_object* v___y_2986_ = _args[9];
lean_object* v___y_2987_ = _args[10];
lean_object* v___y_2988_ = _args[11];
lean_object* v___y_2989_ = _args[12];
lean_object* v___y_2990_ = _args[13];
lean_object* v___y_2991_ = _args[14];
lean_object* v___y_2992_ = _args[15];
lean_object* v___y_2993_ = _args[16];
lean_object* v___y_2994_ = _args[17];
lean_object* v___y_2995_ = _args[18];
lean_object* v___y_2996_ = _args[19];
_start:
{
size_t v_i_boxed_2997_; size_t v_stop_boxed_2998_; lean_object* v_res_2999_; 
v_i_boxed_2997_ = lean_unbox_usize(v_i_2983_);
lean_dec(v_i_2983_);
v_stop_boxed_2998_ = lean_unbox_usize(v_stop_2984_);
lean_dec(v_stop_2984_);
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2977_, v_00_u03b2_2978_, v_00_u03c3_2979_, v_00_u03c3_2980_, v_f_2981_, v_as_2982_, v_i_boxed_2997_, v_stop_boxed_2998_, v_b_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v_as_2982_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3000_, lean_object* v_00_u03c3_3001_, lean_object* v_00_u03b1_3002_, lean_object* v_00_u03b2_3003_, lean_object* v_f_3004_, lean_object* v_keys_3005_, lean_object* v_vals_3006_, lean_object* v_heq_3007_, lean_object* v_i_3008_, lean_object* v_acc_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3004_, v_keys_3005_, v_vals_3006_, v_i_3008_, v_acc_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_3022_ = _args[0];
lean_object* v_00_u03c3_3023_ = _args[1];
lean_object* v_00_u03b1_3024_ = _args[2];
lean_object* v_00_u03b2_3025_ = _args[3];
lean_object* v_f_3026_ = _args[4];
lean_object* v_keys_3027_ = _args[5];
lean_object* v_vals_3028_ = _args[6];
lean_object* v_heq_3029_ = _args[7];
lean_object* v_i_3030_ = _args[8];
lean_object* v_acc_3031_ = _args[9];
lean_object* v___y_3032_ = _args[10];
lean_object* v___y_3033_ = _args[11];
lean_object* v___y_3034_ = _args[12];
lean_object* v___y_3035_ = _args[13];
lean_object* v___y_3036_ = _args[14];
lean_object* v___y_3037_ = _args[15];
lean_object* v___y_3038_ = _args[16];
lean_object* v___y_3039_ = _args[17];
lean_object* v___y_3040_ = _args[18];
lean_object* v___y_3041_ = _args[19];
lean_object* v___y_3042_ = _args[20];
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3022_, v_00_u03c3_3023_, v_00_u03b1_3024_, v_00_u03b2_3025_, v_f_3026_, v_keys_3027_, v_vals_3028_, v_heq_3029_, v_i_3030_, v_acc_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v_vals_3028_);
lean_dec_ref(v_keys_3027_);
return v_res_3043_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(lean_object* v_a_3044_, lean_object* v_x_3045_){
_start:
{
if (lean_obj_tag(v_x_3045_) == 0)
{
uint8_t v___x_3046_; 
v___x_3046_ = 0;
return v___x_3046_;
}
else
{
lean_object* v_head_3047_; lean_object* v_tail_3048_; uint8_t v___x_3049_; 
v_head_3047_ = lean_ctor_get(v_x_3045_, 0);
v_tail_3048_ = lean_ctor_get(v_x_3045_, 1);
v___x_3049_ = lean_nat_dec_eq(v_a_3044_, v_head_3047_);
if (v___x_3049_ == 0)
{
v_x_3045_ = v_tail_3048_;
goto _start;
}
else
{
return v___x_3049_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0___boxed(lean_object* v_a_3051_, lean_object* v_x_3052_){
_start:
{
uint8_t v_res_3053_; lean_object* v_r_3054_; 
v_res_3053_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_a_3051_, v_x_3052_);
lean_dec(v_x_3052_);
lean_dec(v_a_3051_);
v_r_3054_ = lean_box(v_res_3053_);
return v_r_3054_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1));
v___x_3058_ = lean_unsigned_to_nat(6u);
v___x_3059_ = lean_unsigned_to_nat(91u);
v___x_3060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3061_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3062_ = l_mkPanicMessageWithDecl(v___x_3061_, v___x_3060_, v___x_3059_, v___x_3058_, v___x_3057_);
return v___x_3062_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3));
v___x_3065_ = lean_unsigned_to_nat(6u);
v___x_3066_ = lean_unsigned_to_nat(92u);
v___x_3067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3068_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3069_ = l_mkPanicMessageWithDecl(v___x_3068_, v___x_3067_, v___x_3066_, v___x_3065_, v___x_3064_);
return v___x_3069_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5));
v___x_3072_ = lean_unsigned_to_nat(6u);
v___x_3073_ = lean_unsigned_to_nat(93u);
v___x_3074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3075_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3076_ = l_mkPanicMessageWithDecl(v___x_3075_, v___x_3074_, v___x_3073_, v___x_3072_, v___x_3071_);
return v___x_3076_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7));
v___x_3079_ = lean_unsigned_to_nat(6u);
v___x_3080_ = lean_unsigned_to_nat(94u);
v___x_3081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3082_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3083_ = l_mkPanicMessageWithDecl(v___x_3082_, v___x_3081_, v___x_3080_, v___x_3079_, v___x_3078_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(lean_object* v_a_3084_, lean_object* v_as_3085_, size_t v_sz_3086_, size_t v_i_3087_, lean_object* v_b_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_usize_dec_lt(v_i_3087_, v_sz_3086_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_b_3088_);
return v___x_3101_;
}
else
{
lean_object* v_snd_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3158_; 
v_snd_3102_ = lean_ctor_get(v_b_3088_, 1);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_b_3088_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v_b_3088_, 0);
lean_dec(v_unused_3159_);
v___x_3104_ = v_b_3088_;
v_isShared_3105_ = v_isSharedCheck_3158_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_snd_3102_);
lean_dec(v_b_3088_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3158_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v_a_3108_; lean_object* v___y_3119_; lean_object* v_a_3139_; 
v___x_3106_ = lean_box(0);
v_a_3139_ = lean_array_uget_borrowed(v_as_3085_, v_i_3087_);
if (lean_obj_tag(v_a_3139_) == 1)
{
lean_object* v_val_3140_; lean_object* v_p_3141_; uint8_t v___x_3142_; 
v_val_3140_ = lean_ctor_get(v_a_3139_, 0);
v_p_3141_ = lean_ctor_get(v_val_3140_, 0);
v___x_3142_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3144_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3143_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
v___y_3119_ = v___x_3144_;
goto v___jp_3118_;
}
else
{
uint8_t v___x_3145_; 
v___x_3145_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3141_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3147_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3146_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
v___y_3119_ = v___x_3147_;
goto v___jp_3118_;
}
else
{
lean_object* v_elimStack_3148_; uint8_t v___x_3149_; 
v_elimStack_3148_ = lean_ctor_get(v_a_3084_, 11);
v___x_3149_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3102_, v_elimStack_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3151_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3150_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
v___y_3119_ = v___x_3151_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; uint8_t v___x_3155_; 
v___x_3152_ = l_Int_Internal_Linear_Poly_coeff(v_p_3141_, v_snd_3102_);
v___x_3153_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3154_ = lean_int_dec_eq(v___x_3152_, v___x_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_bool_not(v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3157_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3156_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
v___y_3119_ = v___x_3157_;
goto v___jp_3118_;
}
else
{
goto v___jp_3115_;
}
}
}
}
}
else
{
goto v___jp_3115_;
}
v___jp_3107_:
{
lean_object* v___x_3110_; 
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 1, v_a_3108_);
lean_ctor_set(v___x_3104_, 0, v___x_3106_);
v___x_3110_ = v___x_3104_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_a_3108_);
v___x_3110_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
size_t v___x_3111_; size_t v___x_3112_; 
v___x_3111_ = ((size_t)1ULL);
v___x_3112_ = lean_usize_add(v_i_3087_, v___x_3111_);
v_i_3087_ = v___x_3112_;
v_b_3088_ = v___x_3110_;
goto _start;
}
}
v___jp_3115_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_unsigned_to_nat(1u);
v___x_3117_ = lean_nat_add(v_snd_3102_, v___x_3116_);
lean_dec(v_snd_3102_);
v_a_3108_ = v___x_3117_;
goto v___jp_3107_;
}
v___jp_3118_:
{
if (lean_obj_tag(v___y_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3130_; 
v_a_3120_ = lean_ctor_get(v___y_3119_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___y_3119_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3122_ = v___y_3119_;
v_isShared_3123_ = v_isSharedCheck_3130_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___y_3119_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3130_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
if (lean_obj_tag(v_a_3120_) == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3127_; 
lean_del_object(v___x_3104_);
v___x_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_a_3120_);
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3124_);
lean_ctor_set(v___x_3125_, 1, v_snd_3102_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3125_);
v___x_3127_ = v___x_3122_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
else
{
lean_object* v_a_3129_; 
lean_del_object(v___x_3122_);
lean_dec(v_snd_3102_);
v_a_3129_ = lean_ctor_get(v_a_3120_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v_a_3120_, 1);
v_a_3108_ = v_a_3129_;
goto v___jp_3107_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_del_object(v___x_3104_);
lean_dec(v_snd_3102_);
v_a_3131_ = lean_ctor_get(v___y_3119_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___y_3119_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___y_3119_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___y_3119_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_a_3160_, lean_object* v_as_3161_, lean_object* v_sz_3162_, lean_object* v_i_3163_, lean_object* v_b_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
size_t v_sz_boxed_3176_; size_t v_i_boxed_3177_; lean_object* v_res_3178_; 
v_sz_boxed_3176_ = lean_unbox_usize(v_sz_3162_);
lean_dec(v_sz_3162_);
v_i_boxed_3177_ = lean_unbox_usize(v_i_3163_);
lean_dec(v_i_3163_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3160_, v_as_3161_, v_sz_boxed_3176_, v_i_boxed_3177_, v_b_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v_as_3161_);
lean_dec_ref(v_a_3160_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(lean_object* v_a_3179_, lean_object* v_as_3180_, size_t v_sz_3181_, size_t v_i_3182_, lean_object* v_b_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_usize_dec_lt(v_i_3182_, v_sz_3181_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_b_3183_);
return v___x_3196_;
}
else
{
lean_object* v_snd_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3253_; 
v_snd_3197_ = lean_ctor_get(v_b_3183_, 1);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_b_3183_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v_b_3183_, 0);
lean_dec(v_unused_3254_);
v___x_3199_ = v_b_3183_;
v_isShared_3200_ = v_isSharedCheck_3253_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_snd_3197_);
lean_dec(v_b_3183_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3253_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v_a_3203_; lean_object* v___y_3214_; lean_object* v_a_3234_; 
v___x_3201_ = lean_box(0);
v_a_3234_ = lean_array_uget_borrowed(v_as_3180_, v_i_3182_);
if (lean_obj_tag(v_a_3234_) == 1)
{
lean_object* v_val_3235_; lean_object* v_p_3236_; uint8_t v___x_3237_; 
v_val_3235_ = lean_ctor_get(v_a_3234_, 0);
v_p_3236_ = lean_ctor_get(v_val_3235_, 0);
v___x_3237_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3236_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3239_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3238_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
v___y_3214_ = v___x_3239_;
goto v___jp_3213_;
}
else
{
uint8_t v___x_3240_; 
v___x_3240_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3236_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3242_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3241_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
v___y_3214_ = v___x_3242_;
goto v___jp_3213_;
}
else
{
lean_object* v_elimStack_3243_; uint8_t v___x_3244_; 
v_elimStack_3243_ = lean_ctor_get(v_a_3179_, 11);
v___x_3244_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3197_, v_elimStack_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3246_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3245_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
v___y_3214_ = v___x_3246_;
goto v___jp_3213_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; uint8_t v___x_3250_; 
v___x_3247_ = l_Int_Internal_Linear_Poly_coeff(v_p_3236_, v_snd_3197_);
v___x_3248_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3249_ = lean_int_dec_eq(v___x_3247_, v___x_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_bool_not(v___x_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3252_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3251_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
v___y_3214_ = v___x_3252_;
goto v___jp_3213_;
}
else
{
goto v___jp_3210_;
}
}
}
}
}
else
{
goto v___jp_3210_;
}
v___jp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 1, v_a_3203_);
lean_ctor_set(v___x_3199_, 0, v___x_3201_);
v___x_3205_ = v___x_3199_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_a_3203_);
v___x_3205_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
size_t v___x_3206_; size_t v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = ((size_t)1ULL);
v___x_3207_ = lean_usize_add(v_i_3182_, v___x_3206_);
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_3179_, v_as_3180_, v_sz_3181_, v___x_3207_, v___x_3205_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
return v___x_3208_;
}
}
v___jp_3210_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = lean_unsigned_to_nat(1u);
v___x_3212_ = lean_nat_add(v_snd_3197_, v___x_3211_);
lean_dec(v_snd_3197_);
v_a_3203_ = v___x_3212_;
goto v___jp_3202_;
}
v___jp_3213_:
{
if (lean_obj_tag(v___y_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3225_; 
v_a_3215_ = lean_ctor_get(v___y_3214_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___y_3214_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3217_ = v___y_3214_;
v_isShared_3218_ = v_isSharedCheck_3225_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___y_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3225_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
if (lean_obj_tag(v_a_3215_) == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
lean_del_object(v___x_3199_);
v___x_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3219_, 0, v_a_3215_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set(v___x_3220_, 1, v_snd_3197_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3220_);
v___x_3222_ = v___x_3217_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
else
{
lean_object* v_a_3224_; 
lean_del_object(v___x_3217_);
lean_dec(v_snd_3197_);
v_a_3224_ = lean_ctor_get(v_a_3215_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v_a_3215_, 1);
v_a_3203_ = v_a_3224_;
goto v___jp_3202_;
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_del_object(v___x_3199_);
lean_dec(v_snd_3197_);
v_a_3226_ = lean_ctor_get(v___y_3214_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___y_3214_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___y_3214_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___y_3214_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3___boxed(lean_object* v_a_3255_, lean_object* v_as_3256_, lean_object* v_sz_3257_, lean_object* v_i_3258_, lean_object* v_b_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
size_t v_sz_boxed_3271_; size_t v_i_boxed_3272_; lean_object* v_res_3273_; 
v_sz_boxed_3271_ = lean_unbox_usize(v_sz_3257_);
lean_dec(v_sz_3257_);
v_i_boxed_3272_ = lean_unbox_usize(v_i_3258_);
lean_dec(v_i_3258_);
v_res_3273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3255_, v_as_3256_, v_sz_boxed_3271_, v_i_boxed_3272_, v_b_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v_as_3256_);
lean_dec_ref(v_a_3255_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(lean_object* v_init_3274_, lean_object* v_a_3275_, lean_object* v_n_3276_, lean_object* v_b_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
if (lean_obj_tag(v_n_3276_) == 0)
{
lean_object* v_cs_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; size_t v_sz_3292_; size_t v___x_3293_; lean_object* v___x_3294_; 
v_cs_3289_ = lean_ctor_get(v_n_3276_, 0);
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
lean_ctor_set(v___x_3291_, 1, v_b_3277_);
v_sz_3292_ = lean_array_size(v_cs_3289_);
v___x_3293_ = ((size_t)0ULL);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3274_, v_a_3275_, v_cs_3289_, v_sz_3292_, v___x_3293_, v___x_3291_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3309_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3309_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3309_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_fst_3299_; 
v_fst_3299_ = lean_ctor_get(v_a_3295_, 0);
if (lean_obj_tag(v_fst_3299_) == 0)
{
lean_object* v_snd_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
v_snd_3300_ = lean_ctor_get(v_a_3295_, 1);
lean_inc(v_snd_3300_);
lean_dec(v_a_3295_);
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_snd_3300_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3301_);
v___x_3303_ = v___x_3297_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
else
{
lean_object* v_val_3305_; lean_object* v___x_3307_; 
lean_inc_ref(v_fst_3299_);
lean_dec(v_a_3295_);
v_val_3305_ = lean_ctor_get(v_fst_3299_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v_fst_3299_, 1);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v_val_3305_);
v___x_3307_ = v___x_3297_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_val_3305_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
v_a_3310_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3294_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3294_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
else
{
lean_object* v_vs_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; size_t v_sz_3321_; size_t v___x_3322_; lean_object* v___x_3323_; 
v_vs_3318_ = lean_ctor_get(v_n_3276_, 0);
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v_b_3277_);
v_sz_3321_ = lean_array_size(v_vs_3318_);
v___x_3322_ = ((size_t)0ULL);
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_3275_, v_vs_3318_, v_sz_3321_, v___x_3322_, v___x_3320_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3338_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3338_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3338_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v_fst_3328_; 
v_fst_3328_ = lean_ctor_get(v_a_3324_, 0);
if (lean_obj_tag(v_fst_3328_) == 0)
{
lean_object* v_snd_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
v_snd_3329_ = lean_ctor_get(v_a_3324_, 1);
lean_inc(v_snd_3329_);
lean_dec(v_a_3324_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_snd_3329_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3330_);
v___x_3332_ = v___x_3326_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
else
{
lean_object* v_val_3334_; lean_object* v___x_3336_; 
lean_inc_ref(v_fst_3328_);
lean_dec(v_a_3324_);
v_val_3334_ = lean_ctor_get(v_fst_3328_, 0);
lean_inc(v_val_3334_);
lean_dec_ref_known(v_fst_3328_, 1);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v_val_3334_);
v___x_3336_ = v___x_3326_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_val_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
v_a_3339_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3323_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3323_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(lean_object* v_init_3347_, lean_object* v_a_3348_, lean_object* v_as_3349_, size_t v_sz_3350_, size_t v_i_3351_, lean_object* v_b_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
uint8_t v___x_3364_; 
v___x_3364_ = lean_usize_dec_lt(v_i_3351_, v_sz_3350_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_b_3352_);
return v___x_3365_;
}
else
{
lean_object* v_snd_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3400_; 
v_snd_3366_ = lean_ctor_get(v_b_3352_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_b_3352_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v_b_3352_, 0);
lean_dec(v_unused_3401_);
v___x_3368_ = v_b_3352_;
v_isShared_3369_ = v_isSharedCheck_3400_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_snd_3366_);
lean_dec(v_b_3352_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3400_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_a_3370_; lean_object* v___x_3371_; 
v_a_3370_ = lean_array_uget_borrowed(v_as_3349_, v_i_3351_);
lean_inc(v_snd_3366_);
v___x_3371_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3347_, v_a_3348_, v_a_3370_, v_snd_3366_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3391_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3391_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3391_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
if (lean_obj_tag(v_a_3372_) == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
v___x_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3376_, 0, v_a_3372_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v___x_3376_);
v___x_3378_ = v___x_3368_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_snd_3366_);
v___x_3378_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3378_);
v___x_3380_ = v___x_3374_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
lean_del_object(v___x_3374_);
lean_dec(v_snd_3366_);
v_a_3383_ = lean_ctor_get(v_a_3372_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v_a_3372_, 1);
v___x_3384_ = lean_box(0);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v_a_3383_);
lean_ctor_set(v___x_3368_, 0, v___x_3384_);
v___x_3386_ = v___x_3368_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_a_3383_);
v___x_3386_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
size_t v___x_3387_; size_t v___x_3388_; 
v___x_3387_ = ((size_t)1ULL);
v___x_3388_ = lean_usize_add(v_i_3351_, v___x_3387_);
v_i_3351_ = v___x_3388_;
v_b_3352_ = v___x_3386_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_del_object(v___x_3368_);
lean_dec(v_snd_3366_);
v_a_3392_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3371_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3371_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_3402_ = _args[0];
lean_object* v_a_3403_ = _args[1];
lean_object* v_as_3404_ = _args[2];
lean_object* v_sz_3405_ = _args[3];
lean_object* v_i_3406_ = _args[4];
lean_object* v_b_3407_ = _args[5];
lean_object* v___y_3408_ = _args[6];
lean_object* v___y_3409_ = _args[7];
lean_object* v___y_3410_ = _args[8];
lean_object* v___y_3411_ = _args[9];
lean_object* v___y_3412_ = _args[10];
lean_object* v___y_3413_ = _args[11];
lean_object* v___y_3414_ = _args[12];
lean_object* v___y_3415_ = _args[13];
lean_object* v___y_3416_ = _args[14];
lean_object* v___y_3417_ = _args[15];
lean_object* v___y_3418_ = _args[16];
_start:
{
size_t v_sz_boxed_3419_; size_t v_i_boxed_3420_; lean_object* v_res_3421_; 
v_sz_boxed_3419_ = lean_unbox_usize(v_sz_3405_);
lean_dec(v_sz_3405_);
v_i_boxed_3420_ = lean_unbox_usize(v_i_3406_);
lean_dec(v_i_3406_);
v_res_3421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_3402_, v_a_3403_, v_as_3404_, v_sz_boxed_3419_, v_i_boxed_3420_, v_b_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v_as_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_init_3402_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1___boxed(lean_object* v_init_3422_, lean_object* v_a_3423_, lean_object* v_n_3424_, lean_object* v_b_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3422_, v_a_3423_, v_n_3424_, v_b_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v_n_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_init_3422_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(lean_object* v_a_3438_, lean_object* v_as_3439_, size_t v_sz_3440_, size_t v_i_3441_, lean_object* v_b_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v___x_3454_; 
v___x_3454_ = lean_usize_dec_lt(v_i_3441_, v_sz_3440_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; 
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_b_3442_);
return v___x_3455_;
}
else
{
lean_object* v_snd_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3519_; 
v_snd_3456_ = lean_ctor_get(v_b_3442_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_b_3442_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; 
v_unused_3520_ = lean_ctor_get(v_b_3442_, 0);
lean_dec(v_unused_3520_);
v___x_3458_ = v_b_3442_;
v_isShared_3459_ = v_isSharedCheck_3519_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_snd_3456_);
lean_dec(v_b_3442_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3519_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v_a_3462_; lean_object* v___y_3473_; lean_object* v_a_3500_; 
v___x_3460_ = lean_box(0);
v_a_3500_ = lean_array_uget_borrowed(v_as_3439_, v_i_3441_);
if (lean_obj_tag(v_a_3500_) == 1)
{
lean_object* v_val_3501_; lean_object* v_p_3502_; uint8_t v___x_3503_; 
v_val_3501_ = lean_ctor_get(v_a_3500_, 0);
v_p_3502_ = lean_ctor_get(v_val_3501_, 0);
v___x_3503_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3502_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3505_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3504_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
v___y_3473_ = v___x_3505_;
goto v___jp_3472_;
}
else
{
uint8_t v___x_3506_; 
v___x_3506_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3502_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3508_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3507_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
v___y_3473_ = v___x_3508_;
goto v___jp_3472_;
}
else
{
lean_object* v_elimStack_3509_; uint8_t v___x_3510_; 
v_elimStack_3509_ = lean_ctor_get(v_a_3438_, 11);
v___x_3510_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3456_, v_elimStack_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3512_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3511_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
v___y_3473_ = v___x_3512_;
goto v___jp_3472_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; uint8_t v___x_3516_; 
v___x_3513_ = l_Int_Internal_Linear_Poly_coeff(v_p_3502_, v_snd_3456_);
v___x_3514_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3515_ = lean_int_dec_eq(v___x_3513_, v___x_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_bool_not(v___x_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3518_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3517_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
v___y_3473_ = v___x_3518_;
goto v___jp_3472_;
}
else
{
goto v___jp_3469_;
}
}
}
}
}
else
{
goto v___jp_3469_;
}
v___jp_3461_:
{
lean_object* v___x_3464_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_a_3462_);
lean_ctor_set(v___x_3458_, 0, v___x_3460_);
v___x_3464_ = v___x_3458_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_a_3462_);
v___x_3464_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
size_t v___x_3465_; size_t v___x_3466_; 
v___x_3465_ = ((size_t)1ULL);
v___x_3466_ = lean_usize_add(v_i_3441_, v___x_3465_);
v_i_3441_ = v___x_3466_;
v_b_3442_ = v___x_3464_;
goto _start;
}
}
v___jp_3469_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = lean_unsigned_to_nat(1u);
v___x_3471_ = lean_nat_add(v_snd_3456_, v___x_3470_);
lean_dec(v_snd_3456_);
v_a_3462_ = v___x_3471_;
goto v___jp_3461_;
}
v___jp_3472_:
{
if (lean_obj_tag(v___y_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3491_; 
v_a_3474_ = lean_ctor_get(v___y_3473_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___y_3473_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3476_ = v___y_3473_;
v_isShared_3477_ = v_isSharedCheck_3491_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___y_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3491_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
if (lean_obj_tag(v_a_3474_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3489_; 
lean_del_object(v___x_3458_);
v_a_3478_ = lean_ctor_get(v_a_3474_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v_a_3474_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3480_ = v_a_3474_;
v_isShared_3481_ = v_isSharedCheck_3489_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v_a_3474_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3489_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set_tag(v___x_3480_, 1);
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v_snd_3456_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3484_);
v___x_3486_ = v___x_3476_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_a_3490_; 
lean_del_object(v___x_3476_);
lean_dec(v_snd_3456_);
v_a_3490_ = lean_ctor_get(v_a_3474_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v_a_3474_, 1);
v_a_3462_ = v_a_3490_;
goto v___jp_3461_;
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_del_object(v___x_3458_);
lean_dec(v_snd_3456_);
v_a_3492_ = lean_ctor_get(v___y_3473_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___y_3473_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___y_3473_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___y_3473_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5___boxed(lean_object* v_a_3521_, lean_object* v_as_3522_, lean_object* v_sz_3523_, lean_object* v_i_3524_, lean_object* v_b_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
size_t v_sz_boxed_3537_; size_t v_i_boxed_3538_; lean_object* v_res_3539_; 
v_sz_boxed_3537_ = lean_unbox_usize(v_sz_3523_);
lean_dec(v_sz_3523_);
v_i_boxed_3538_ = lean_unbox_usize(v_i_3524_);
lean_dec(v_i_3524_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3521_, v_as_3522_, v_sz_boxed_3537_, v_i_boxed_3538_, v_b_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v_as_3522_);
lean_dec_ref(v_a_3521_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(lean_object* v_a_3540_, lean_object* v_as_3541_, size_t v_sz_3542_, size_t v_i_3543_, lean_object* v_b_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
uint8_t v___x_3556_; 
v___x_3556_ = lean_usize_dec_lt(v_i_3543_, v_sz_3542_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_b_3544_);
return v___x_3557_;
}
else
{
lean_object* v_snd_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3621_; 
v_snd_3558_ = lean_ctor_get(v_b_3544_, 1);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_b_3544_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; 
v_unused_3622_ = lean_ctor_get(v_b_3544_, 0);
lean_dec(v_unused_3622_);
v___x_3560_ = v_b_3544_;
v_isShared_3561_ = v_isSharedCheck_3621_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_snd_3558_);
lean_dec(v_b_3544_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3621_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v_a_3564_; lean_object* v___y_3575_; lean_object* v_a_3602_; 
v___x_3562_ = lean_box(0);
v_a_3602_ = lean_array_uget_borrowed(v_as_3541_, v_i_3543_);
if (lean_obj_tag(v_a_3602_) == 1)
{
lean_object* v_val_3603_; lean_object* v_p_3604_; uint8_t v___x_3605_; 
v_val_3603_ = lean_ctor_get(v_a_3602_, 0);
v_p_3604_ = lean_ctor_get(v_val_3603_, 0);
v___x_3605_ = l_Int_Internal_Linear_Poly_isSorted(v_p_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
v___x_3607_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3606_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
v___y_3575_ = v___x_3607_;
goto v___jp_3574_;
}
else
{
uint8_t v___x_3608_; 
v___x_3608_ = l_Int_Internal_Linear_Poly_checkCoeffs(v_p_3604_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
v___x_3610_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3609_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
v___y_3575_ = v___x_3610_;
goto v___jp_3574_;
}
else
{
lean_object* v_elimStack_3611_; uint8_t v___x_3612_; 
v_elimStack_3611_ = lean_ctor_get(v_a_3540_, 11);
v___x_3612_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_3558_, v_elimStack_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
v___x_3614_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3613_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
v___y_3575_ = v___x_3614_;
goto v___jp_3574_;
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; uint8_t v___x_3618_; 
v___x_3615_ = l_Int_Internal_Linear_Poly_coeff(v_p_3604_, v_snd_3558_);
v___x_3616_ = lean_obj_once(&l_Int_Internal_Linear_Poly_checkCoeffs___closed__0, &l_Int_Internal_Linear_Poly_checkCoeffs___closed__0_once, _init_l_Int_Internal_Linear_Poly_checkCoeffs___closed__0);
v___x_3617_ = lean_int_dec_eq(v___x_3615_, v___x_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_bool_not(v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
v___x_3620_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(v___x_3619_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
v___y_3575_ = v___x_3620_;
goto v___jp_3574_;
}
else
{
goto v___jp_3571_;
}
}
}
}
}
else
{
goto v___jp_3571_;
}
v___jp_3563_:
{
lean_object* v___x_3566_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 1, v_a_3564_);
lean_ctor_set(v___x_3560_, 0, v___x_3562_);
v___x_3566_ = v___x_3560_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_a_3564_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
size_t v___x_3567_; size_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = ((size_t)1ULL);
v___x_3568_ = lean_usize_add(v_i_3543_, v___x_3567_);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_3540_, v_as_3541_, v_sz_3542_, v___x_3568_, v___x_3566_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3569_;
}
}
v___jp_3571_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = lean_unsigned_to_nat(1u);
v___x_3573_ = lean_nat_add(v_snd_3558_, v___x_3572_);
lean_dec(v_snd_3558_);
v_a_3564_ = v___x_3573_;
goto v___jp_3563_;
}
v___jp_3574_:
{
if (lean_obj_tag(v___y_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3593_; 
v_a_3576_ = lean_ctor_get(v___y_3575_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___y_3575_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3578_ = v___y_3575_;
v_isShared_3579_ = v_isSharedCheck_3593_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___y_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3593_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
if (lean_obj_tag(v_a_3576_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3560_);
v_a_3580_ = lean_ctor_get(v_a_3576_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_a_3576_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3582_ = v_a_3576_;
v_isShared_3583_ = v_isSharedCheck_3591_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v_a_3576_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3591_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set_tag(v___x_3582_, 1);
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
lean_ctor_set(v___x_3586_, 1, v_snd_3558_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3586_);
v___x_3588_ = v___x_3578_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
else
{
lean_object* v_a_3592_; 
lean_del_object(v___x_3578_);
lean_dec(v_snd_3558_);
v_a_3592_ = lean_ctor_get(v_a_3576_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v_a_3576_, 1);
v_a_3564_ = v_a_3592_;
goto v___jp_3563_;
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
v_a_3594_ = lean_ctor_get(v___y_3575_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___y_3575_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___y_3575_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___y_3575_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2___boxed(lean_object* v_a_3623_, lean_object* v_as_3624_, lean_object* v_sz_3625_, lean_object* v_i_3626_, lean_object* v_b_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
size_t v_sz_boxed_3639_; size_t v_i_boxed_3640_; lean_object* v_res_3641_; 
v_sz_boxed_3639_ = lean_unbox_usize(v_sz_3625_);
lean_dec(v_sz_3625_);
v_i_boxed_3640_ = lean_unbox_usize(v_i_3626_);
lean_dec(v_i_3626_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3623_, v_as_3624_, v_sz_boxed_3639_, v_i_boxed_3640_, v_b_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v_as_3624_);
lean_dec_ref(v_a_3623_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(lean_object* v_a_3642_, lean_object* v_t_3643_, lean_object* v_init_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_root_3656_; lean_object* v_tail_3657_; lean_object* v___x_3658_; 
v_root_3656_ = lean_ctor_get(v_t_3643_, 0);
v_tail_3657_ = lean_ctor_get(v_t_3643_, 1);
lean_inc(v_init_3644_);
v___x_3658_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_3644_, v_a_3642_, v_root_3656_, v_init_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v_init_3644_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3695_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3695_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3695_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
if (lean_obj_tag(v_a_3659_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3665_; 
v_a_3663_ = lean_ctor_get(v_a_3659_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v_a_3659_, 1);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v_a_3663_);
v___x_3665_ = v___x_3661_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; size_t v_sz_3670_; size_t v___x_3671_; lean_object* v___x_3672_; 
lean_del_object(v___x_3661_);
v_a_3667_ = lean_ctor_get(v_a_3659_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v_a_3659_, 1);
v___x_3668_ = lean_box(0);
v___x_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
lean_ctor_set(v___x_3669_, 1, v_a_3667_);
v_sz_3670_ = lean_array_size(v_tail_3657_);
v___x_3671_ = ((size_t)0ULL);
v___x_3672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_3642_, v_tail_3657_, v_sz_3670_, v___x_3671_, v___x_3669_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3686_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3686_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3686_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_fst_3677_; 
v_fst_3677_ = lean_ctor_get(v_a_3673_, 0);
if (lean_obj_tag(v_fst_3677_) == 0)
{
lean_object* v_snd_3678_; lean_object* v___x_3680_; 
v_snd_3678_ = lean_ctor_get(v_a_3673_, 1);
lean_inc(v_snd_3678_);
lean_dec(v_a_3673_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v_snd_3678_);
v___x_3680_ = v___x_3675_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_snd_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
else
{
lean_object* v_val_3682_; lean_object* v___x_3684_; 
lean_inc_ref(v_fst_3677_);
lean_dec(v_a_3673_);
v_val_3682_ = lean_ctor_get(v_fst_3677_, 0);
lean_inc(v_val_3682_);
lean_dec_ref_known(v_fst_3677_, 1);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v_val_3682_);
v___x_3684_ = v___x_3675_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_val_3682_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
v_a_3687_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3672_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3672_);
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
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
v_a_3696_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3658_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3658_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1___boxed(lean_object* v_a_3704_, lean_object* v_t_3705_, lean_object* v_init_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3704_, v_t_3705_, v_init_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v_t_3705_);
lean_dec_ref(v_a_3704_);
return v_res_3718_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3720_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0));
v___x_3721_ = lean_unsigned_to_nat(2u);
v___x_3722_ = lean_unsigned_to_nat(87u);
v___x_3723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0));
v___x_3724_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3725_ = l_mkPanicMessageWithDecl(v___x_3724_, v___x_3723_, v___x_3722_, v___x_3721_, v___x_3720_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3726_, v_a_3734_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v_elimEqs_3739_; lean_object* v_vars_3740_; lean_object* v_size_3741_; lean_object* v_size_3742_; uint8_t v___x_3743_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3737_, 1);
v_elimEqs_3739_ = lean_ctor_get(v_a_3738_, 10);
lean_inc_ref(v_elimEqs_3739_);
v_vars_3740_ = lean_ctor_get(v_a_3738_, 0);
v_size_3741_ = lean_ctor_get(v_elimEqs_3739_, 2);
v_size_3742_ = lean_ctor_get(v_vars_3740_, 2);
v___x_3743_ = lean_nat_dec_eq(v_size_3741_, v_size_3742_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_dec_ref(v_elimEqs_3739_);
lean_dec(v_a_3738_);
v___x_3744_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1);
v___x_3745_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_3744_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
return v___x_3745_;
}
else
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = lean_unsigned_to_nat(0u);
v___x_3747_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_3738_, v_elimEqs_3739_, v___x_3746_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_elimEqs_3739_);
lean_dec(v_a_3738_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3755_; 
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v___x_3747_, 0);
lean_dec(v_unused_3756_);
v___x_3749_ = v___x_3747_;
v_isShared_3750_ = v_isSharedCheck_3755_;
goto v_resetjp_3748_;
}
else
{
lean_dec(v___x_3747_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3755_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3751_ = lean_box(0);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3751_);
v___x_3753_ = v___x_3749_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
v_a_3757_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3747_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3747_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
v_a_3765_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3737_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3737_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___boxed(lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec(v_a_3773_);
return v_res_3784_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3787_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1));
v___x_3788_ = lean_unsigned_to_nat(4u);
v___x_3789_ = lean_unsigned_to_nat(99u);
v___x_3790_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0));
v___x_3791_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_3792_ = l_mkPanicMessageWithDecl(v___x_3791_, v___x_3790_, v___x_3789_, v___x_3788_, v___x_3787_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(lean_object* v_as_x27_3793_, lean_object* v_b_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
if (lean_obj_tag(v_as_x27_3793_) == 0)
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v_b_3794_);
return v___x_3806_;
}
else
{
lean_object* v_head_3807_; lean_object* v_tail_3808_; lean_object* v___x_3809_; 
v_head_3807_ = lean_ctor_get(v_as_x27_3793_, 0);
v_tail_3808_ = lean_ctor_get(v_as_x27_3793_, 1);
v___x_3809_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_head_3807_, v___y_3795_, v___y_3803_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; uint8_t v___x_3811_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = lean_unbox(v_a_3810_);
lean_dec(v_a_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2);
v___x_3813_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(v___x_3812_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3824_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3816_ = v___x_3813_;
v_isShared_3817_ = v_isSharedCheck_3824_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3813_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3824_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
if (lean_obj_tag(v_a_3814_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3820_; 
v_a_3818_ = lean_ctor_get(v_a_3814_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v_a_3814_, 1);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v_a_3818_);
v___x_3820_ = v___x_3816_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3818_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
else
{
lean_object* v_a_3822_; 
lean_del_object(v___x_3816_);
v_a_3822_ = lean_ctor_get(v_a_3814_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v_a_3814_, 1);
v_as_x27_3793_ = v_tail_3808_;
v_b_3794_ = v_a_3822_;
goto _start;
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3813_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3813_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_box(0);
v_as_x27_3793_ = v_tail_3808_;
v_b_3794_ = v___x_3833_;
goto _start;
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
v_a_3835_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3809_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3809_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___boxed(lean_object* v_as_x27_3843_, lean_object* v_b_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3843_, v_b_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec(v_as_x27_3843_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3857_, v_a_3865_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v_elimStack_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v_elimStack_3870_ = lean_ctor_get(v_a_3869_, 11);
lean_inc(v_elimStack_3870_);
lean_dec(v_a_3869_);
v___x_3871_ = lean_box(0);
v___x_3872_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_elimStack_3870_, v___x_3871_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
lean_dec(v_elimStack_3870_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3879_ == 0)
{
lean_object* v_unused_3880_; 
v_unused_3880_ = lean_ctor_get(v___x_3872_, 0);
lean_dec(v_unused_3880_);
v___x_3874_ = v___x_3872_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_dec(v___x_3872_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3871_);
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3871_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
else
{
return v___x_3872_;
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
v_a_3881_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3868_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3868_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack___boxed(lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec(v_a_3889_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(lean_object* v_as_3901_, lean_object* v_as_x27_3902_, lean_object* v_b_3903_, lean_object* v_a_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_as_x27_3902_, v_b_3903_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___boxed(lean_object* v_as_3917_, lean_object* v_as_x27_3918_, lean_object* v_b_3919_, lean_object* v_a_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(v_as_3917_, v_as_x27_3918_, v_b_3919_, v_a_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec(v_as_x27_3918_);
lean_dec(v_as_3917_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(lean_object* v_____s_3936_, lean_object* v_as_3937_, size_t v_sz_3938_, size_t v_i_3939_, lean_object* v_b_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
uint8_t v___x_3952_; 
v___x_3952_ = lean_usize_dec_lt(v_i_3939_, v_sz_3938_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v_b_3940_);
return v___x_3953_;
}
else
{
lean_object* v_a_3954_; lean_object* v_p_3955_; lean_object* v___x_3956_; 
lean_dec_ref(v_b_3940_);
v_a_3954_ = lean_array_uget_borrowed(v_as_3937_, v_i_3939_);
v_p_3955_ = lean_ctor_get(v_a_3954_, 0);
v___x_3956_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_3955_, v_____s_3936_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v___x_3957_; size_t v___x_3958_; size_t v___x_3959_; 
lean_dec_ref_known(v___x_3956_, 1);
v___x_3957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_3958_ = ((size_t)1ULL);
v___x_3959_ = lean_usize_add(v_i_3939_, v___x_3958_);
v_i_3939_ = v___x_3959_;
v_b_3940_ = v___x_3957_;
goto _start;
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
v_a_3961_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3956_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3956_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(lean_object* v_____s_3969_, lean_object* v_as_3970_, lean_object* v_sz_3971_, lean_object* v_i_3972_, lean_object* v_b_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
size_t v_sz_boxed_3985_; size_t v_i_boxed_3986_; lean_object* v_res_3987_; 
v_sz_boxed_3985_ = lean_unbox_usize(v_sz_3971_);
lean_dec(v_sz_3971_);
v_i_boxed_3986_ = lean_unbox_usize(v_i_3972_);
lean_dec(v_i_3972_);
v_res_3987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3969_, v_as_3970_, v_sz_boxed_3985_, v_i_boxed_3986_, v_b_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v_as_3970_);
lean_dec(v_____s_3969_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(lean_object* v_____s_3988_, lean_object* v_as_3989_, size_t v_sz_3990_, size_t v_i_3991_, lean_object* v_b_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
uint8_t v___x_4004_; 
v___x_4004_ = lean_usize_dec_lt(v_i_3991_, v_sz_3990_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v_b_3992_);
return v___x_4005_;
}
else
{
lean_object* v_a_4006_; lean_object* v_p_4007_; lean_object* v___x_4008_; 
lean_dec_ref(v_b_3992_);
v_a_4006_ = lean_array_uget_borrowed(v_as_3989_, v_i_3991_);
v_p_4007_ = lean_ctor_get(v_a_4006_, 0);
v___x_4008_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4007_, v_____s_3988_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v___x_4009_; size_t v___x_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
lean_dec_ref_known(v___x_4008_, 1);
v___x_4009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0));
v___x_4010_ = ((size_t)1ULL);
v___x_4011_ = lean_usize_add(v_i_3991_, v___x_4010_);
v___x_4012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_3988_, v_as_3989_, v_sz_3990_, v___x_4011_, v___x_4009_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
return v___x_4012_;
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
v_a_4013_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4008_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4008_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1___boxed(lean_object* v_____s_4021_, lean_object* v_as_4022_, lean_object* v_sz_4023_, lean_object* v_i_4024_, lean_object* v_b_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
size_t v_sz_boxed_4037_; size_t v_i_boxed_4038_; lean_object* v_res_4039_; 
v_sz_boxed_4037_ = lean_unbox_usize(v_sz_4023_);
lean_dec(v_sz_4023_);
v_i_boxed_4038_ = lean_unbox_usize(v_i_4024_);
lean_dec(v_i_4024_);
v_res_4039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4021_, v_as_4022_, v_sz_boxed_4037_, v_i_boxed_4038_, v_b_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v_as_4022_);
lean_dec(v_____s_4021_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(lean_object* v_____s_4043_, lean_object* v_as_4044_, size_t v_sz_4045_, size_t v_i_4046_, lean_object* v_b_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
uint8_t v___x_4059_; 
v___x_4059_ = lean_usize_dec_lt(v_i_4046_, v_sz_4045_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_b_4047_);
return v___x_4060_;
}
else
{
lean_object* v_a_4061_; lean_object* v_p_4062_; lean_object* v___x_4063_; 
lean_dec_ref(v_b_4047_);
v_a_4061_ = lean_array_uget_borrowed(v_as_4044_, v_i_4046_);
v_p_4062_ = lean_ctor_get(v_a_4061_, 0);
v___x_4063_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4062_, v_____s_4043_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v___x_4064_; size_t v___x_4065_; size_t v___x_4066_; 
lean_dec_ref_known(v___x_4063_, 1);
v___x_4064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4065_ = ((size_t)1ULL);
v___x_4066_ = lean_usize_add(v_i_4046_, v___x_4065_);
v_i_4046_ = v___x_4066_;
v_b_4047_ = v___x_4064_;
goto _start;
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
v_a_4068_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4063_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4063_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_____s_4076_, lean_object* v_as_4077_, lean_object* v_sz_4078_, lean_object* v_i_4079_, lean_object* v_b_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
size_t v_sz_boxed_4092_; size_t v_i_boxed_4093_; lean_object* v_res_4094_; 
v_sz_boxed_4092_ = lean_unbox_usize(v_sz_4078_);
lean_dec(v_sz_4078_);
v_i_boxed_4093_ = lean_unbox_usize(v_i_4079_);
lean_dec(v_i_4079_);
v_res_4094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4076_, v_as_4077_, v_sz_boxed_4092_, v_i_boxed_4093_, v_b_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v_as_4077_);
lean_dec(v_____s_4076_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(lean_object* v_____s_4095_, lean_object* v_as_4096_, size_t v_sz_4097_, size_t v_i_4098_, lean_object* v_b_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
uint8_t v___x_4111_; 
v___x_4111_ = lean_usize_dec_lt(v_i_4098_, v_sz_4097_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v_b_4099_);
return v___x_4112_;
}
else
{
lean_object* v_a_4113_; lean_object* v_p_4114_; lean_object* v___x_4115_; 
lean_dec_ref(v_b_4099_);
v_a_4113_ = lean_array_uget_borrowed(v_as_4096_, v_i_4098_);
v_p_4114_ = lean_ctor_get(v_a_4113_, 0);
v___x_4115_ = l_Int_Internal_Linear_Poly_checkCnstrOf(v_p_4114_, v_____s_4095_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v___x_4116_; size_t v___x_4117_; size_t v___x_4118_; lean_object* v___x_4119_; 
lean_dec_ref_known(v___x_4115_, 1);
v___x_4116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_4117_ = ((size_t)1ULL);
v___x_4118_ = lean_usize_add(v_i_4098_, v___x_4117_);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_4095_, v_as_4096_, v_sz_4097_, v___x_4118_, v___x_4116_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4119_;
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
v_a_4120_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4115_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4115_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_____s_4128_, lean_object* v_as_4129_, lean_object* v_sz_4130_, lean_object* v_i_4131_, lean_object* v_b_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
size_t v_sz_boxed_4144_; size_t v_i_boxed_4145_; lean_object* v_res_4146_; 
v_sz_boxed_4144_ = lean_unbox_usize(v_sz_4130_);
lean_dec(v_sz_4130_);
v_i_boxed_4145_ = lean_unbox_usize(v_i_4131_);
lean_dec(v_i_4131_);
v_res_4146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4128_, v_as_4129_, v_sz_boxed_4144_, v_i_boxed_4145_, v_b_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(lean_object* v_init_4147_, lean_object* v_____s_4148_, lean_object* v_n_4149_, lean_object* v_b_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
if (lean_obj_tag(v_n_4149_) == 0)
{
lean_object* v_cs_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; size_t v_sz_4165_; size_t v___x_4166_; lean_object* v___x_4167_; 
v_cs_4162_ = lean_ctor_get(v_n_4149_, 0);
v___x_4163_ = lean_box(0);
v___x_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
lean_ctor_set(v___x_4164_, 1, v_b_4150_);
v_sz_4165_ = lean_array_size(v_cs_4162_);
v___x_4166_ = ((size_t)0ULL);
v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4147_, v_____s_4148_, v_cs_4162_, v_sz_4165_, v___x_4166_, v___x_4164_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4182_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4170_ = v___x_4167_;
v_isShared_4171_ = v_isSharedCheck_4182_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4182_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v_fst_4172_; 
v_fst_4172_ = lean_ctor_get(v_a_4168_, 0);
if (lean_obj_tag(v_fst_4172_) == 0)
{
lean_object* v_snd_4173_; lean_object* v___x_4174_; lean_object* v___x_4176_; 
v_snd_4173_ = lean_ctor_get(v_a_4168_, 1);
lean_inc(v_snd_4173_);
lean_dec(v_a_4168_);
v___x_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4174_, 0, v_snd_4173_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 0, v___x_4174_);
v___x_4176_ = v___x_4170_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
else
{
lean_object* v_val_4178_; lean_object* v___x_4180_; 
lean_inc_ref(v_fst_4172_);
lean_dec(v_a_4168_);
v_val_4178_ = lean_ctor_get(v_fst_4172_, 0);
lean_inc(v_val_4178_);
lean_dec_ref_known(v_fst_4172_, 1);
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 0, v_val_4178_);
v___x_4180_ = v___x_4170_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_val_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4167_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4167_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
else
{
lean_object* v_vs_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; size_t v_sz_4194_; size_t v___x_4195_; lean_object* v___x_4196_; 
v_vs_4191_ = lean_ctor_get(v_n_4149_, 0);
v___x_4192_ = lean_box(0);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
lean_ctor_set(v___x_4193_, 1, v_b_4150_);
v_sz_4194_ = lean_array_size(v_vs_4191_);
v___x_4195_ = ((size_t)0ULL);
v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_4148_, v_vs_4191_, v_sz_4194_, v___x_4195_, v___x_4193_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4211_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4199_ = v___x_4196_;
v_isShared_4200_ = v_isSharedCheck_4211_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4211_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v_fst_4201_; 
v_fst_4201_ = lean_ctor_get(v_a_4197_, 0);
if (lean_obj_tag(v_fst_4201_) == 0)
{
lean_object* v_snd_4202_; lean_object* v___x_4203_; lean_object* v___x_4205_; 
v_snd_4202_ = lean_ctor_get(v_a_4197_, 1);
lean_inc(v_snd_4202_);
lean_dec(v_a_4197_);
v___x_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4203_, 0, v_snd_4202_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___x_4203_);
v___x_4205_ = v___x_4199_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4203_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
else
{
lean_object* v_val_4207_; lean_object* v___x_4209_; 
lean_inc_ref(v_fst_4201_);
lean_dec(v_a_4197_);
v_val_4207_ = lean_ctor_get(v_fst_4201_, 0);
lean_inc(v_val_4207_);
lean_dec_ref_known(v_fst_4201_, 1);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_val_4207_);
v___x_4209_ = v___x_4199_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_val_4207_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
v_a_4212_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4196_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4196_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_4220_, lean_object* v_____s_4221_, lean_object* v_as_4222_, size_t v_sz_4223_, size_t v_i_4224_, lean_object* v_b_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
uint8_t v___x_4237_; 
v___x_4237_ = lean_usize_dec_lt(v_i_4224_, v_sz_4223_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_b_4225_);
return v___x_4238_;
}
else
{
lean_object* v_snd_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4273_; 
v_snd_4239_ = lean_ctor_get(v_b_4225_, 1);
v_isSharedCheck_4273_ = !lean_is_exclusive(v_b_4225_);
if (v_isSharedCheck_4273_ == 0)
{
lean_object* v_unused_4274_; 
v_unused_4274_ = lean_ctor_get(v_b_4225_, 0);
lean_dec(v_unused_4274_);
v___x_4241_ = v_b_4225_;
v_isShared_4242_ = v_isSharedCheck_4273_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_snd_4239_);
lean_dec(v_b_4225_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4273_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v_a_4243_; lean_object* v___x_4244_; 
v_a_4243_ = lean_array_uget_borrowed(v_as_4222_, v_i_4224_);
lean_inc(v_snd_4239_);
v___x_4244_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4220_, v_____s_4221_, v_a_4243_, v_snd_4239_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4264_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4247_ = v___x_4244_;
v_isShared_4248_ = v_isSharedCheck_4264_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4244_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4264_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
if (lean_obj_tag(v_a_4245_) == 0)
{
lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4249_, 0, v_a_4245_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v___x_4249_);
v___x_4251_ = v___x_4241_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4249_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_snd_4239_);
v___x_4251_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4253_; 
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v___x_4251_);
v___x_4253_ = v___x_4247_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4257_; lean_object* v___x_4259_; 
lean_del_object(v___x_4247_);
lean_dec(v_snd_4239_);
v_a_4256_ = lean_ctor_get(v_a_4245_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v_a_4245_, 1);
v___x_4257_ = lean_box(0);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 1, v_a_4256_);
lean_ctor_set(v___x_4241_, 0, v___x_4257_);
v___x_4259_ = v___x_4241_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4257_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v_a_4256_);
v___x_4259_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
size_t v___x_4260_; size_t v___x_4261_; 
v___x_4260_ = ((size_t)1ULL);
v___x_4261_ = lean_usize_add(v_i_4224_, v___x_4260_);
v_i_4224_ = v___x_4261_;
v_b_4225_ = v___x_4259_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_del_object(v___x_4241_);
lean_dec(v_snd_4239_);
v_a_4265_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4244_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4244_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_4275_ = _args[0];
lean_object* v_____s_4276_ = _args[1];
lean_object* v_as_4277_ = _args[2];
lean_object* v_sz_4278_ = _args[3];
lean_object* v_i_4279_ = _args[4];
lean_object* v_b_4280_ = _args[5];
lean_object* v___y_4281_ = _args[6];
lean_object* v___y_4282_ = _args[7];
lean_object* v___y_4283_ = _args[8];
lean_object* v___y_4284_ = _args[9];
lean_object* v___y_4285_ = _args[10];
lean_object* v___y_4286_ = _args[11];
lean_object* v___y_4287_ = _args[12];
lean_object* v___y_4288_ = _args[13];
lean_object* v___y_4289_ = _args[14];
lean_object* v___y_4290_ = _args[15];
lean_object* v___y_4291_ = _args[16];
_start:
{
size_t v_sz_boxed_4292_; size_t v_i_boxed_4293_; lean_object* v_res_4294_; 
v_sz_boxed_4292_ = lean_unbox_usize(v_sz_4278_);
lean_dec(v_sz_4278_);
v_i_boxed_4293_ = lean_unbox_usize(v_i_4279_);
lean_dec(v_i_4279_);
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_4275_, v_____s_4276_, v_as_4277_, v_sz_boxed_4292_, v_i_boxed_4293_, v_b_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v_as_4277_);
lean_dec(v_____s_4276_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0___boxed(lean_object* v_init_4295_, lean_object* v_____s_4296_, lean_object* v_n_4297_, lean_object* v_b_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4295_, v_____s_4296_, v_n_4297_, v_b_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v_n_4297_);
lean_dec(v_____s_4296_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(lean_object* v_____s_4311_, lean_object* v_t_4312_, lean_object* v_init_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_root_4325_; lean_object* v_tail_4326_; lean_object* v___x_4327_; 
v_root_4325_ = lean_ctor_get(v_t_4312_, 0);
v_tail_4326_ = lean_ctor_get(v_t_4312_, 1);
v___x_4327_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_4313_, v_____s_4311_, v_root_4325_, v_init_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4364_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4330_ = v___x_4327_;
v_isShared_4331_ = v_isSharedCheck_4364_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4327_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4364_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
if (lean_obj_tag(v_a_4328_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4334_; 
v_a_4332_ = lean_ctor_get(v_a_4328_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v_a_4328_, 1);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v_a_4332_);
v___x_4334_ = v___x_4330_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; size_t v_sz_4339_; size_t v___x_4340_; lean_object* v___x_4341_; 
lean_del_object(v___x_4330_);
v_a_4336_ = lean_ctor_get(v_a_4328_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v_a_4328_, 1);
v___x_4337_ = lean_box(0);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
lean_ctor_set(v___x_4338_, 1, v_a_4336_);
v_sz_4339_ = lean_array_size(v_tail_4326_);
v___x_4340_ = ((size_t)0ULL);
v___x_4341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_4311_, v_tail_4326_, v_sz_4339_, v___x_4340_, v___x_4338_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4355_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4344_ = v___x_4341_;
v_isShared_4345_ = v_isSharedCheck_4355_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4341_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4355_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v_fst_4346_; 
v_fst_4346_ = lean_ctor_get(v_a_4342_, 0);
if (lean_obj_tag(v_fst_4346_) == 0)
{
lean_object* v_snd_4347_; lean_object* v___x_4349_; 
v_snd_4347_ = lean_ctor_get(v_a_4342_, 1);
lean_inc(v_snd_4347_);
lean_dec(v_a_4342_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v_snd_4347_);
v___x_4349_ = v___x_4344_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_snd_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
else
{
lean_object* v_val_4351_; lean_object* v___x_4353_; 
lean_inc_ref(v_fst_4346_);
lean_dec(v_a_4342_);
v_val_4351_ = lean_ctor_get(v_fst_4346_, 0);
lean_inc(v_val_4351_);
lean_dec_ref_known(v_fst_4346_, 1);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v_val_4351_);
v___x_4353_ = v___x_4344_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_val_4351_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v_a_4356_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4341_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4341_);
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
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
v_a_4365_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4327_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4327_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0___boxed(lean_object* v_____s_4373_, lean_object* v_t_4374_, lean_object* v_init_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_____s_4373_, v_t_4374_, v_init_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec(v___y_4376_);
lean_dec_ref(v_t_4374_);
lean_dec(v_____s_4373_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(lean_object* v_as_4388_, size_t v_sz_4389_, size_t v_i_4390_, lean_object* v_b_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
uint8_t v___x_4403_; 
v___x_4403_ = lean_usize_dec_lt(v_i_4390_, v_sz_4389_);
if (v___x_4403_ == 0)
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v_b_4391_);
return v___x_4404_;
}
else
{
lean_object* v_snd_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4429_; 
v_snd_4405_ = lean_ctor_get(v_b_4391_, 1);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_b_4391_);
if (v_isSharedCheck_4429_ == 0)
{
lean_object* v_unused_4430_; 
v_unused_4430_ = lean_ctor_get(v_b_4391_, 0);
lean_dec(v_unused_4430_);
v___x_4407_ = v_b_4391_;
v_isShared_4408_ = v_isSharedCheck_4429_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_snd_4405_);
lean_dec(v_b_4391_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4429_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v_a_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_a_4409_ = lean_array_uget_borrowed(v_as_4388_, v_i_4390_);
v___x_4410_ = lean_box(0);
v___x_4411_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4405_, v_a_4409_, v___x_4410_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
lean_dec_ref_known(v___x_4411_, 1);
v___x_4412_ = lean_box(0);
v___x_4413_ = lean_unsigned_to_nat(1u);
v___x_4414_ = lean_nat_add(v_snd_4405_, v___x_4413_);
lean_dec(v_snd_4405_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 1, v___x_4414_);
lean_ctor_set(v___x_4407_, 0, v___x_4412_);
v___x_4416_ = v___x_4407_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4412_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
size_t v___x_4417_; size_t v___x_4418_; 
v___x_4417_ = ((size_t)1ULL);
v___x_4418_ = lean_usize_add(v_i_4390_, v___x_4417_);
v_i_4390_ = v___x_4418_;
v_b_4391_ = v___x_4416_;
goto _start;
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_del_object(v___x_4407_);
lean_dec(v_snd_4405_);
v_a_4421_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4411_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4411_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_as_4431_, lean_object* v_sz_4432_, lean_object* v_i_4433_, lean_object* v_b_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
size_t v_sz_boxed_4446_; size_t v_i_boxed_4447_; lean_object* v_res_4448_; 
v_sz_boxed_4446_ = lean_unbox_usize(v_sz_4432_);
lean_dec(v_sz_4432_);
v_i_boxed_4447_ = lean_unbox_usize(v_i_4433_);
lean_dec(v_i_4433_);
v_res_4448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4431_, v_sz_boxed_4446_, v_i_boxed_4447_, v_b_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
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
lean_dec_ref(v_as_4431_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(lean_object* v_as_4449_, size_t v_sz_4450_, size_t v_i_4451_, lean_object* v_b_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
uint8_t v___x_4464_; 
v___x_4464_ = lean_usize_dec_lt(v_i_4451_, v_sz_4450_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; 
v___x_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4465_, 0, v_b_4452_);
return v___x_4465_;
}
else
{
lean_object* v_snd_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4490_; 
v_snd_4466_ = lean_ctor_get(v_b_4452_, 1);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_b_4452_);
if (v_isSharedCheck_4490_ == 0)
{
lean_object* v_unused_4491_; 
v_unused_4491_ = lean_ctor_get(v_b_4452_, 0);
lean_dec(v_unused_4491_);
v___x_4468_ = v_b_4452_;
v_isShared_4469_ = v_isSharedCheck_4490_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_snd_4466_);
lean_dec(v_b_4452_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4490_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v_a_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v_a_4470_ = lean_array_uget_borrowed(v_as_4449_, v_i_4451_);
v___x_4471_ = lean_box(0);
v___x_4472_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4466_, v_a_4470_, v___x_4471_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4477_; 
lean_dec_ref_known(v___x_4472_, 1);
v___x_4473_ = lean_box(0);
v___x_4474_ = lean_unsigned_to_nat(1u);
v___x_4475_ = lean_nat_add(v_snd_4466_, v___x_4474_);
lean_dec(v_snd_4466_);
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 1, v___x_4475_);
lean_ctor_set(v___x_4468_, 0, v___x_4473_);
v___x_4477_ = v___x_4468_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v___x_4475_);
v___x_4477_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
size_t v___x_4478_; size_t v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = ((size_t)1ULL);
v___x_4479_ = lean_usize_add(v_i_4451_, v___x_4478_);
v___x_4480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_4449_, v_sz_4450_, v___x_4479_, v___x_4477_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
return v___x_4480_;
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
lean_del_object(v___x_4468_);
lean_dec(v_snd_4466_);
v_a_4482_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4472_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4472_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(lean_object* v_as_4492_, lean_object* v_sz_4493_, lean_object* v_i_4494_, lean_object* v_b_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
size_t v_sz_boxed_4507_; size_t v_i_boxed_4508_; lean_object* v_res_4509_; 
v_sz_boxed_4507_ = lean_unbox_usize(v_sz_4493_);
lean_dec(v_sz_4493_);
v_i_boxed_4508_ = lean_unbox_usize(v_i_4494_);
lean_dec(v_i_4494_);
v_res_4509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_4492_, v_sz_boxed_4507_, v_i_boxed_4508_, v_b_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v_as_4492_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(lean_object* v_init_4510_, lean_object* v_n_4511_, lean_object* v_b_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
if (lean_obj_tag(v_n_4511_) == 0)
{
lean_object* v_cs_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; size_t v_sz_4527_; size_t v___x_4528_; lean_object* v___x_4529_; 
v_cs_4524_ = lean_ctor_get(v_n_4511_, 0);
v___x_4525_ = lean_box(0);
v___x_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
lean_ctor_set(v___x_4526_, 1, v_b_4512_);
v_sz_4527_ = lean_array_size(v_cs_4524_);
v___x_4528_ = ((size_t)0ULL);
v___x_4529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4510_, v_cs_4524_, v_sz_4527_, v___x_4528_, v___x_4526_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4544_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4532_ = v___x_4529_;
v_isShared_4533_ = v_isSharedCheck_4544_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4529_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4544_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v_fst_4534_; 
v_fst_4534_ = lean_ctor_get(v_a_4530_, 0);
if (lean_obj_tag(v_fst_4534_) == 0)
{
lean_object* v_snd_4535_; lean_object* v___x_4536_; lean_object* v___x_4538_; 
v_snd_4535_ = lean_ctor_get(v_a_4530_, 1);
lean_inc(v_snd_4535_);
lean_dec(v_a_4530_);
v___x_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4536_, 0, v_snd_4535_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4536_);
v___x_4538_ = v___x_4532_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
else
{
lean_object* v_val_4540_; lean_object* v___x_4542_; 
lean_inc_ref(v_fst_4534_);
lean_dec(v_a_4530_);
v_val_4540_ = lean_ctor_get(v_fst_4534_, 0);
lean_inc(v_val_4540_);
lean_dec_ref_known(v_fst_4534_, 1);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v_val_4540_);
v___x_4542_ = v___x_4532_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_val_4540_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
v_a_4545_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4529_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4529_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
else
{
lean_object* v_vs_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; size_t v_sz_4556_; size_t v___x_4557_; lean_object* v___x_4558_; 
v_vs_4553_ = lean_ctor_get(v_n_4511_, 0);
v___x_4554_ = lean_box(0);
v___x_4555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
lean_ctor_set(v___x_4555_, 1, v_b_4512_);
v_sz_4556_ = lean_array_size(v_vs_4553_);
v___x_4557_ = ((size_t)0ULL);
v___x_4558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_4553_, v_sz_4556_, v___x_4557_, v___x_4555_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4573_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4561_ = v___x_4558_;
v_isShared_4562_ = v_isSharedCheck_4573_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4558_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4573_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v_fst_4563_; 
v_fst_4563_ = lean_ctor_get(v_a_4559_, 0);
if (lean_obj_tag(v_fst_4563_) == 0)
{
lean_object* v_snd_4564_; lean_object* v___x_4565_; lean_object* v___x_4567_; 
v_snd_4564_ = lean_ctor_get(v_a_4559_, 1);
lean_inc(v_snd_4564_);
lean_dec(v_a_4559_);
v___x_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4565_, 0, v_snd_4564_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4565_);
v___x_4567_ = v___x_4561_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
else
{
lean_object* v_val_4569_; lean_object* v___x_4571_; 
lean_inc_ref(v_fst_4563_);
lean_dec(v_a_4559_);
v_val_4569_ = lean_ctor_get(v_fst_4563_, 0);
lean_inc(v_val_4569_);
lean_dec_ref_known(v_fst_4563_, 1);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v_val_4569_);
v___x_4571_ = v___x_4561_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_val_4569_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
v_a_4574_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4558_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4558_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(lean_object* v_init_4582_, lean_object* v_as_4583_, size_t v_sz_4584_, size_t v_i_4585_, lean_object* v_b_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
uint8_t v___x_4598_; 
v___x_4598_ = lean_usize_dec_lt(v_i_4585_, v_sz_4584_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; 
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v_b_4586_);
return v___x_4599_;
}
else
{
lean_object* v_snd_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4634_; 
v_snd_4600_ = lean_ctor_get(v_b_4586_, 1);
v_isSharedCheck_4634_ = !lean_is_exclusive(v_b_4586_);
if (v_isSharedCheck_4634_ == 0)
{
lean_object* v_unused_4635_; 
v_unused_4635_ = lean_ctor_get(v_b_4586_, 0);
lean_dec(v_unused_4635_);
v___x_4602_ = v_b_4586_;
v_isShared_4603_ = v_isSharedCheck_4634_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_snd_4600_);
lean_dec(v_b_4586_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4634_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v_a_4604_; lean_object* v___x_4605_; 
v_a_4604_ = lean_array_uget_borrowed(v_as_4583_, v_i_4585_);
lean_inc(v_snd_4600_);
v___x_4605_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4582_, v_a_4604_, v_snd_4600_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4625_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4608_ = v___x_4605_;
v_isShared_4609_ = v_isSharedCheck_4625_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4605_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4625_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
if (lean_obj_tag(v_a_4606_) == 0)
{
lean_object* v___x_4610_; lean_object* v___x_4612_; 
v___x_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4610_, 0, v_a_4606_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4610_);
v___x_4612_ = v___x_4602_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v_snd_4600_);
v___x_4612_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4614_; 
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v___x_4612_);
v___x_4614_ = v___x_4608_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
lean_del_object(v___x_4608_);
lean_dec(v_snd_4600_);
v_a_4617_ = lean_ctor_get(v_a_4606_, 0);
lean_inc(v_a_4617_);
lean_dec_ref_known(v_a_4606_, 1);
v___x_4618_ = lean_box(0);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 1, v_a_4617_);
lean_ctor_set(v___x_4602_, 0, v___x_4618_);
v___x_4620_ = v___x_4602_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4618_);
lean_ctor_set(v_reuseFailAlloc_4624_, 1, v_a_4617_);
v___x_4620_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
size_t v___x_4621_; size_t v___x_4622_; 
v___x_4621_ = ((size_t)1ULL);
v___x_4622_ = lean_usize_add(v_i_4585_, v___x_4621_);
v_i_4585_ = v___x_4622_;
v_b_4586_ = v___x_4620_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
lean_del_object(v___x_4602_);
lean_dec(v_snd_4600_);
v_a_4626_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___x_4605_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4605_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(lean_object* v_init_4636_, lean_object* v_as_4637_, lean_object* v_sz_4638_, lean_object* v_i_4639_, lean_object* v_b_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
size_t v_sz_boxed_4652_; size_t v_i_boxed_4653_; lean_object* v_res_4654_; 
v_sz_boxed_4652_ = lean_unbox_usize(v_sz_4638_);
lean_dec(v_sz_4638_);
v_i_boxed_4653_ = lean_unbox_usize(v_i_4639_);
lean_dec(v_i_4639_);
v_res_4654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_4636_, v_as_4637_, v_sz_boxed_4652_, v_i_boxed_4653_, v_b_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v_as_4637_);
lean_dec(v_init_4636_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3___boxed(lean_object* v_init_4655_, lean_object* v_n_4656_, lean_object* v_b_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4655_, v_n_4656_, v_b_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v_n_4656_);
lean_dec(v_init_4655_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(lean_object* v_as_4670_, size_t v_sz_4671_, size_t v_i_4672_, lean_object* v_b_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
uint8_t v___x_4685_; 
v___x_4685_ = lean_usize_dec_lt(v_i_4672_, v_sz_4671_);
if (v___x_4685_ == 0)
{
lean_object* v___x_4686_; 
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v_b_4673_);
return v___x_4686_;
}
else
{
lean_object* v_snd_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4711_; 
v_snd_4687_ = lean_ctor_get(v_b_4673_, 1);
v_isSharedCheck_4711_ = !lean_is_exclusive(v_b_4673_);
if (v_isSharedCheck_4711_ == 0)
{
lean_object* v_unused_4712_; 
v_unused_4712_ = lean_ctor_get(v_b_4673_, 0);
lean_dec(v_unused_4712_);
v___x_4689_ = v_b_4673_;
v_isShared_4690_ = v_isSharedCheck_4711_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_snd_4687_);
lean_dec(v_b_4673_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4711_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v_a_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v_a_4691_ = lean_array_uget_borrowed(v_as_4670_, v_i_4672_);
v___x_4692_ = lean_box(0);
v___x_4693_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4687_, v_a_4691_, v___x_4692_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4698_; 
lean_dec_ref_known(v___x_4693_, 1);
v___x_4694_ = lean_box(0);
v___x_4695_ = lean_unsigned_to_nat(1u);
v___x_4696_ = lean_nat_add(v_snd_4687_, v___x_4695_);
lean_dec(v_snd_4687_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 1, v___x_4696_);
lean_ctor_set(v___x_4689_, 0, v___x_4694_);
v___x_4698_ = v___x_4689_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4694_);
lean_ctor_set(v_reuseFailAlloc_4702_, 1, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
size_t v___x_4699_; size_t v___x_4700_; 
v___x_4699_ = ((size_t)1ULL);
v___x_4700_ = lean_usize_add(v_i_4672_, v___x_4699_);
v_i_4672_ = v___x_4700_;
v_b_4673_ = v___x_4698_;
goto _start;
}
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_del_object(v___x_4689_);
lean_dec(v_snd_4687_);
v_a_4703_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4693_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4693_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(lean_object* v_as_4713_, lean_object* v_sz_4714_, lean_object* v_i_4715_, lean_object* v_b_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
size_t v_sz_boxed_4728_; size_t v_i_boxed_4729_; lean_object* v_res_4730_; 
v_sz_boxed_4728_ = lean_unbox_usize(v_sz_4714_);
lean_dec(v_sz_4714_);
v_i_boxed_4729_ = lean_unbox_usize(v_i_4715_);
lean_dec(v_i_4715_);
v_res_4730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4713_, v_sz_boxed_4728_, v_i_boxed_4729_, v_b_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v_as_4713_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(lean_object* v_as_4731_, size_t v_sz_4732_, size_t v_i_4733_, lean_object* v_b_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
uint8_t v___x_4746_; 
v___x_4746_ = lean_usize_dec_lt(v_i_4733_, v_sz_4732_);
if (v___x_4746_ == 0)
{
lean_object* v___x_4747_; 
v___x_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4747_, 0, v_b_4734_);
return v___x_4747_;
}
else
{
lean_object* v_snd_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4772_; 
v_snd_4748_ = lean_ctor_get(v_b_4734_, 1);
v_isSharedCheck_4772_ = !lean_is_exclusive(v_b_4734_);
if (v_isSharedCheck_4772_ == 0)
{
lean_object* v_unused_4773_; 
v_unused_4773_ = lean_ctor_get(v_b_4734_, 0);
lean_dec(v_unused_4773_);
v___x_4750_ = v_b_4734_;
v_isShared_4751_ = v_isSharedCheck_4772_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_snd_4748_);
lean_dec(v_b_4734_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4772_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v_a_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v_a_4752_ = lean_array_uget_borrowed(v_as_4731_, v_i_4733_);
v___x_4753_ = lean_box(0);
v___x_4754_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_4748_, v_a_4752_, v___x_4753_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4759_; 
lean_dec_ref_known(v___x_4754_, 1);
v___x_4755_ = lean_box(0);
v___x_4756_ = lean_unsigned_to_nat(1u);
v___x_4757_ = lean_nat_add(v_snd_4748_, v___x_4756_);
lean_dec(v_snd_4748_);
if (v_isShared_4751_ == 0)
{
lean_ctor_set(v___x_4750_, 1, v___x_4757_);
lean_ctor_set(v___x_4750_, 0, v___x_4755_);
v___x_4759_ = v___x_4750_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4763_, 1, v___x_4757_);
v___x_4759_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
size_t v___x_4760_; size_t v___x_4761_; lean_object* v___x_4762_; 
v___x_4760_ = ((size_t)1ULL);
v___x_4761_ = lean_usize_add(v_i_4733_, v___x_4760_);
v___x_4762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_4731_, v_sz_4732_, v___x_4761_, v___x_4759_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
return v___x_4762_;
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_del_object(v___x_4750_);
lean_dec(v_snd_4748_);
v_a_4764_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4754_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4754_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4___boxed(lean_object* v_as_4774_, lean_object* v_sz_4775_, lean_object* v_i_4776_, lean_object* v_b_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
size_t v_sz_boxed_4789_; size_t v_i_boxed_4790_; lean_object* v_res_4791_; 
v_sz_boxed_4789_ = lean_unbox_usize(v_sz_4775_);
lean_dec(v_sz_4775_);
v_i_boxed_4790_ = lean_unbox_usize(v_i_4776_);
lean_dec(v_i_4776_);
v_res_4791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_as_4774_, v_sz_boxed_4789_, v_i_boxed_4790_, v_b_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(lean_object* v_t_4792_, lean_object* v_init_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_){
_start:
{
lean_object* v_root_4805_; lean_object* v_tail_4806_; lean_object* v___x_4807_; 
v_root_4805_ = lean_ctor_get(v_t_4792_, 0);
v_tail_4806_ = lean_ctor_get(v_t_4792_, 1);
lean_inc(v_init_4793_);
v___x_4807_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_4793_, v_root_4805_, v_init_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
lean_dec(v_init_4793_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4844_; 
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4810_ = v___x_4807_;
v_isShared_4811_ = v_isSharedCheck_4844_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4807_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4844_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
if (lean_obj_tag(v_a_4808_) == 0)
{
lean_object* v_a_4812_; lean_object* v___x_4814_; 
v_a_4812_ = lean_ctor_get(v_a_4808_, 0);
lean_inc(v_a_4812_);
lean_dec_ref_known(v_a_4808_, 1);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v_a_4812_);
v___x_4814_ = v___x_4810_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4812_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; size_t v_sz_4819_; size_t v___x_4820_; lean_object* v___x_4821_; 
lean_del_object(v___x_4810_);
v_a_4816_ = lean_ctor_get(v_a_4808_, 0);
lean_inc(v_a_4816_);
lean_dec_ref_known(v_a_4808_, 1);
v___x_4817_ = lean_box(0);
v___x_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4817_);
lean_ctor_set(v___x_4818_, 1, v_a_4816_);
v_sz_4819_ = lean_array_size(v_tail_4806_);
v___x_4820_ = ((size_t)0ULL);
v___x_4821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_tail_4806_, v_sz_4819_, v___x_4820_, v___x_4818_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4835_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4824_ = v___x_4821_;
v_isShared_4825_ = v_isSharedCheck_4835_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4821_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4835_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v_fst_4826_; 
v_fst_4826_ = lean_ctor_get(v_a_4822_, 0);
if (lean_obj_tag(v_fst_4826_) == 0)
{
lean_object* v_snd_4827_; lean_object* v___x_4829_; 
v_snd_4827_ = lean_ctor_get(v_a_4822_, 1);
lean_inc(v_snd_4827_);
lean_dec(v_a_4822_);
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 0, v_snd_4827_);
v___x_4829_ = v___x_4824_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_snd_4827_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
else
{
lean_object* v_val_4831_; lean_object* v___x_4833_; 
lean_inc_ref(v_fst_4826_);
lean_dec(v_a_4822_);
v_val_4831_ = lean_ctor_get(v_fst_4826_, 0);
lean_inc(v_val_4831_);
lean_dec_ref_known(v_fst_4826_, 1);
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 0, v_val_4831_);
v___x_4833_ = v___x_4824_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_val_4831_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
else
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4843_; 
v_a_4836_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4838_ = v___x_4821_;
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4821_);
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
}
else
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4852_; 
v_a_4845_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4847_ = v___x_4807_;
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4807_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4850_; 
if (v_isShared_4848_ == 0)
{
v___x_4850_ = v___x_4847_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1___boxed(lean_object* v_t_4853_, lean_object* v_init_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_t_4853_, v_init_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
lean_dec(v___y_4864_);
lean_dec_ref(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v_t_4853_);
return v_res_4866_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4869_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1));
v___x_4870_ = lean_unsigned_to_nat(2u);
v___x_4871_ = lean_unsigned_to_nat(103u);
v___x_4872_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0));
v___x_4873_ = ((lean_object*)(l_Int_Internal_Linear_Poly_checkNoElimVars___closed__0));
v___x_4874_ = l_mkPanicMessageWithDecl(v___x_4873_, v___x_4872_, v___x_4871_, v___x_4870_, v___x_4869_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v___x_4886_; 
v___x_4886_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4875_, v_a_4883_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v_vars_4888_; lean_object* v_diseqs_4889_; lean_object* v_size_4890_; lean_object* v_size_4891_; uint8_t v___x_4892_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
lean_dec_ref_known(v___x_4886_, 1);
v_vars_4888_ = lean_ctor_get(v_a_4887_, 0);
lean_inc_ref(v_vars_4888_);
v_diseqs_4889_ = lean_ctor_get(v_a_4887_, 9);
lean_inc_ref(v_diseqs_4889_);
lean_dec(v_a_4887_);
v_size_4890_ = lean_ctor_get(v_vars_4888_, 2);
lean_inc(v_size_4890_);
lean_dec_ref(v_vars_4888_);
v_size_4891_ = lean_ctor_get(v_diseqs_4889_, 2);
v___x_4892_ = lean_nat_dec_eq(v_size_4890_, v_size_4891_);
lean_dec(v_size_4890_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
lean_dec_ref(v_diseqs_4889_);
v___x_4893_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2);
v___x_4894_ = l_panic___at___00Int_Internal_Linear_Poly_checkNoElimVars_spec__0(v___x_4893_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
return v___x_4894_;
}
else
{
lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = lean_unsigned_to_nat(0u);
v___x_4896_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_diseqs_4889_, v___x_4895_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
lean_dec_ref(v_diseqs_4889_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4904_; 
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4904_ == 0)
{
lean_object* v_unused_4905_; 
v_unused_4905_ = lean_ctor_get(v___x_4896_, 0);
lean_dec(v_unused_4905_);
v___x_4898_ = v___x_4896_;
v_isShared_4899_ = v_isSharedCheck_4904_;
goto v_resetjp_4897_;
}
else
{
lean_dec(v___x_4896_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4904_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4900_; lean_object* v___x_4902_; 
v___x_4900_ = lean_box(0);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v___x_4900_);
v___x_4902_ = v___x_4898_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4900_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4913_; 
v_a_4906_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4908_ = v___x_4896_;
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4896_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4911_; 
if (v_isShared_4909_ == 0)
{
v___x_4911_ = v___x_4908_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_a_4906_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
}
}
else
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
v_a_4914_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4886_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4886_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___boxed(lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
lean_dec(v_a_4927_);
lean_dec_ref(v_a_4926_);
lean_dec(v_a_4925_);
lean_dec_ref(v_a_4924_);
lean_dec(v_a_4923_);
lean_dec(v_a_4922_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v___x_4945_; 
v___x_4945_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v___x_4946_; 
lean_dec_ref_known(v___x_4945_, 1);
v___x_4946_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v___x_4947_; 
lean_dec_ref_known(v___x_4946_, 1);
v___x_4947_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_object* v___x_4948_; 
lean_dec_ref_known(v___x_4947_, 1);
v___x_4948_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v___x_4949_; 
lean_dec_ref_known(v___x_4948_, 1);
v___x_4949_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v___x_4950_; 
lean_dec_ref_known(v___x_4949_, 1);
v___x_4950_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v___x_4951_; 
lean_dec_ref_known(v___x_4950_, 1);
v___x_4951_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
return v___x_4951_;
}
else
{
return v___x_4950_;
}
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
lean_dec(v_a_4959_);
lean_dec_ref(v_a_4958_);
lean_dec(v_a_4957_);
lean_dec_ref(v_a_4956_);
lean_dec(v_a_4955_);
lean_dec_ref(v_a_4954_);
lean_dec(v_a_4953_);
lean_dec(v_a_4952_);
return v_res_4963_;
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
