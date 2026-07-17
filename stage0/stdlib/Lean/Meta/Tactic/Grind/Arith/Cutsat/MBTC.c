// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.MBTC
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Tactic.Grind.MBTC import Lean.Meta.Tactic.Grind.Arith.ModelUtil import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1(lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Rat_ofInt(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(lean_object* v_as_x27_14_, lean_object* v_b_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
if (lean_obj_tag(v_as_x27_14_) == 0)
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_b_15_);
return v___x_22_;
}
else
{
lean_object* v_head_23_; lean_object* v_tail_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
lean_dec_ref(v_b_15_);
v_head_23_ = lean_ctor_get(v_as_x27_14_, 0);
v_tail_24_ = lean_ctor_get(v_as_x27_14_, 1);
v___x_25_ = lean_box(0);
v___x_26_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0));
lean_inc(v_head_23_);
v___x_27_ = l_Lean_Expr_cleanupAnnotations(v_head_23_);
v___x_28_ = l_Lean_Expr_isApp(v___x_27_);
if (v___x_28_ == 0)
{
lean_dec_ref(v___x_27_);
v_as_x27_14_ = v_tail_24_;
v_b_15_ = v___x_26_;
goto _start;
}
else
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = l_Lean_Expr_appFnCleanup___redArg(v___x_27_);
v___x_31_ = l_Lean_Expr_isApp(v___x_30_);
if (v___x_31_ == 0)
{
lean_dec_ref(v___x_30_);
v_as_x27_14_ = v_tail_24_;
v_b_15_ = v___x_26_;
goto _start;
}
else
{
lean_object* v_arg_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_arg_33_ = lean_ctor_get(v___x_30_, 1);
lean_inc_ref(v_arg_33_);
v___x_34_ = l_Lean_Expr_appFnCleanup___redArg(v___x_30_);
v___x_35_ = l_Lean_Expr_isApp(v___x_34_);
if (v___x_35_ == 0)
{
lean_dec_ref(v___x_34_);
lean_dec_ref(v_arg_33_);
v_as_x27_14_ = v_tail_24_;
v_b_15_ = v___x_26_;
goto _start;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_34_);
v___x_38_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__3));
v___x_39_ = l_Lean_Expr_isConstOf(v___x_37_, v___x_38_);
lean_dec_ref(v___x_37_);
if (v___x_39_ == 0)
{
lean_dec_ref(v_arg_33_);
v_as_x27_14_ = v_tail_24_;
v_b_15_ = v___x_26_;
goto _start;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_41_ = l_Lean_Expr_cleanupAnnotations(v_arg_33_);
v___x_42_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__5));
v___x_43_ = l_Lean_Expr_isConstOf(v___x_41_, v___x_42_);
lean_dec_ref(v___x_41_);
if (v___x_43_ == 0)
{
v_as_x27_14_ = v_tail_24_;
v_b_15_ = v___x_26_;
goto _start;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_st_ref_get(v___y_16_);
lean_inc(v_head_23_);
v___x_46_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v___x_45_, v_head_23_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___x_45_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_56_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_56_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_56_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_56_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v_a_47_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_25_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_52_);
v___x_54_ = v___x_49_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
else
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
v_a_57_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v___x_46_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_46_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_a_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___boxed(lean_object* v_as_x27_65_, lean_object* v_b_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(v_as_x27_65_, v_b_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec(v_as_x27_65_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_74_, lean_object* v_vals_75_, lean_object* v_i_76_, lean_object* v_k_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_array_get_size(v_keys_74_);
v___x_79_ = lean_nat_dec_lt(v_i_76_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_dec(v_i_76_);
v___x_80_ = lean_box(0);
return v___x_80_;
}
else
{
lean_object* v_k_x27_81_; size_t v___x_82_; size_t v___x_83_; uint8_t v___x_84_; 
v_k_x27_81_ = lean_array_fget_borrowed(v_keys_74_, v_i_76_);
v___x_82_ = lean_ptr_addr(v_k_77_);
v___x_83_ = lean_ptr_addr(v_k_x27_81_);
v___x_84_ = lean_usize_dec_eq(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_i_76_, v___x_85_);
lean_dec(v_i_76_);
v_i_76_ = v___x_86_;
goto _start;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_array_fget_borrowed(v_vals_75_, v_i_76_);
lean_dec(v_i_76_);
lean_inc(v___x_88_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_90_, lean_object* v_vals_91_, lean_object* v_i_92_, lean_object* v_k_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(v_keys_90_, v_vals_91_, v_i_92_, v_k_93_);
lean_dec_ref(v_k_93_);
lean_dec_ref(v_vals_91_);
lean_dec_ref(v_keys_90_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(lean_object* v_x_95_, size_t v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v_es_98_; lean_object* v___x_99_; size_t v___x_100_; size_t v___x_101_; lean_object* v_j_102_; lean_object* v___x_103_; 
v_es_98_ = lean_ctor_get(v_x_95_, 0);
v___x_99_ = lean_box(2);
v___x_100_ = ((size_t)31ULL);
v___x_101_ = lean_usize_land(v_x_96_, v___x_100_);
v_j_102_ = lean_usize_to_nat(v___x_101_);
v___x_103_ = lean_array_get_borrowed(v___x_99_, v_es_98_, v_j_102_);
lean_dec(v_j_102_);
switch(lean_obj_tag(v___x_103_))
{
case 0:
{
lean_object* v_key_104_; lean_object* v_val_105_; size_t v___x_106_; size_t v___x_107_; uint8_t v___x_108_; 
v_key_104_ = lean_ctor_get(v___x_103_, 0);
v_val_105_ = lean_ctor_get(v___x_103_, 1);
v___x_106_ = lean_ptr_addr(v_x_97_);
v___x_107_ = lean_ptr_addr(v_key_104_);
v___x_108_ = lean_usize_dec_eq(v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
lean_object* v___x_110_; 
lean_inc(v_val_105_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v_val_105_);
return v___x_110_;
}
}
case 1:
{
lean_object* v_node_111_; size_t v___x_112_; size_t v___x_113_; 
v_node_111_ = lean_ctor_get(v___x_103_, 0);
v___x_112_ = ((size_t)5ULL);
v___x_113_ = lean_usize_shift_right(v_x_96_, v___x_112_);
v_x_95_ = v_node_111_;
v_x_96_ = v___x_113_;
goto _start;
}
default: 
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
return v___x_115_;
}
}
}
else
{
lean_object* v_ks_116_; lean_object* v_vs_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_ks_116_ = lean_ctor_get(v_x_95_, 0);
v_vs_117_ = lean_ctor_get(v_x_95_, 1);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(v_ks_116_, v_vs_117_, v___x_118_, v_x_97_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
size_t v_x_52294__boxed_123_; lean_object* v_res_124_; 
v_x_52294__boxed_123_ = lean_unbox_usize(v_x_121_);
lean_dec(v_x_121_);
v_res_124_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(v_x_120_, v_x_52294__boxed_123_, v_x_122_);
lean_dec_ref(v_x_122_);
lean_dec_ref(v_x_120_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; uint64_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; 
v___x_127_ = lean_ptr_addr(v_x_126_);
v___x_128_ = ((size_t)3ULL);
v___x_129_ = lean_usize_shift_right(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_to_uint64(v___x_129_);
v___x_131_ = lean_uint64_to_usize(v___x_130_);
v___x_132_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(v_x_125_, v___x_131_, v_x_126_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg___boxed(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_x_133_, v_x_134_);
lean_dec_ref(v_x_134_);
lean_dec_ref(v_x_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(lean_object* v_e_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_val_149_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_st_ref_get(v_a_137_);
lean_inc_ref(v_e_136_);
v___x_217_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v___x_216_, v_e_136_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
if (lean_obj_tag(v_a_218_) == 1)
{
lean_object* v_val_219_; 
lean_dec_ref(v_e_136_);
v_val_219_ = lean_ctor_get(v_a_218_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v_a_218_, 1);
v_val_149_ = v_val_219_;
goto v___jp_148_;
}
else
{
lean_object* v___x_220_; 
lean_dec(v_a_218_);
lean_inc(v_a_146_);
lean_inc_ref(v_a_145_);
lean_inc(v_a_144_);
lean_inc_ref(v_a_143_);
lean_inc_ref(v_e_136_);
v___x_220_ = lean_infer_type(v_e_136_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_281_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_281_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_281_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_281_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = l_Lean_Int_mkType;
v___x_226_ = lean_expr_eqv(v_a_221_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; uint8_t v___x_228_; 
lean_del_object(v___x_223_);
v___x_227_ = l_Lean_Nat_mkType;
v___x_228_ = lean_expr_eqv(v_a_221_, v___x_227_);
lean_dec(v_a_221_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_137_, v_a_145_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v_toIntVarMap_231_; lean_object* v___x_232_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
v_toIntVarMap_231_ = lean_ctor_get(v_a_230_, 22);
lean_inc_ref(v_toIntVarMap_231_);
lean_dec(v_a_230_);
v___x_232_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_toIntVarMap_231_, v_e_136_);
lean_dec_ref(v_toIntVarMap_231_);
if (lean_obj_tag(v___x_232_) == 1)
{
lean_object* v_val_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_val_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = lean_st_ref_get(v_a_137_);
v___x_235_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v___x_234_, v_val_233_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
if (lean_obj_tag(v_a_236_) == 1)
{
lean_object* v_val_237_; 
lean_dec_ref(v_e_136_);
v_val_237_ = lean_ctor_get(v_a_236_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v_a_236_, 1);
v_val_149_ = v_val_237_;
goto v___jp_148_;
}
else
{
lean_dec(v_a_236_);
v___y_156_ = v_a_137_;
v___y_157_ = v_a_143_;
v___y_158_ = v_a_144_;
v___y_159_ = v_a_145_;
v___y_160_ = v_a_146_;
goto v___jp_155_;
}
}
else
{
lean_dec_ref(v_e_136_);
return v___x_235_;
}
}
else
{
lean_dec(v___x_232_);
v___y_156_ = v_a_137_;
v___y_157_ = v_a_143_;
v___y_158_ = v_a_144_;
v___y_159_ = v_a_145_;
v___y_160_ = v_a_146_;
goto v___jp_155_;
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v_e_136_);
v_a_238_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_229_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_229_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Meta_Grind_getParents___redArg(v_e_136_, v_a_137_);
lean_dec_ref(v_e_136_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
v___x_248_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_247_);
lean_dec(v_a_247_);
v___x_249_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg___closed__0));
v___x_250_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(v___x_248_, v___x_249_, v_a_137_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v___x_248_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_260_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_260_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_fst_255_; 
v_fst_255_ = lean_ctor_get(v_a_251_, 0);
lean_inc(v_fst_255_);
lean_dec(v_a_251_);
if (lean_obj_tag(v_fst_255_) == 0)
{
lean_del_object(v___x_253_);
goto v___jp_152_;
}
else
{
lean_object* v_val_256_; lean_object* v___x_258_; 
v_val_256_ = lean_ctor_get(v_fst_255_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v_fst_255_, 1);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v_val_256_);
v___x_258_ = v___x_253_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_val_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_250_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_250_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_246_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_246_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_279_; 
lean_dec(v_a_221_);
lean_dec_ref(v_e_136_);
v___x_277_ = lean_box(0);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_277_);
v___x_279_ = v___x_223_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
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
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec_ref(v_e_136_);
v_a_282_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_220_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_220_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_136_);
return v___x_217_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v_val_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
v___jp_152_:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
v___jp_155_:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_156_, v___y_159_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v_toIntTermMap_163_; lean_object* v___x_164_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref_known(v___x_161_, 1);
v_toIntTermMap_163_ = lean_ctor_get(v_a_162_, 21);
lean_inc_ref(v_toIntTermMap_163_);
lean_dec(v_a_162_);
v___x_164_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_toIntTermMap_163_, v_e_136_);
lean_dec_ref(v_e_136_);
lean_dec_ref(v_toIntTermMap_163_);
if (lean_obj_tag(v___x_164_) == 1)
{
lean_object* v_val_165_; lean_object* v_eToInt_166_; lean_object* v___x_167_; 
v_val_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_164_, 1);
v_eToInt_166_ = lean_ctor_get(v_val_165_, 0);
lean_inc_ref_n(v_eToInt_166_, 2);
lean_dec(v_val_165_);
v___x_167_ = l_Lean_Meta_getIntValue_x3f(v_eToInt_166_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_199_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_199_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_199_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_199_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
if (lean_obj_tag(v_a_168_) == 1)
{
lean_object* v_val_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_183_; 
lean_dec_ref(v_eToInt_166_);
v_val_172_ = lean_ctor_get(v_a_168_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_a_168_);
if (v_isSharedCheck_183_ == 0)
{
v___x_174_ = v_a_168_;
v_isShared_175_ = v_isSharedCheck_183_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_val_172_);
lean_dec(v_a_168_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_183_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_176_ = l_Rat_ofInt(v_val_172_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_176_);
v___x_178_ = v___x_174_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_182_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_178_);
v___x_180_ = v___x_170_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v___x_184_; 
lean_del_object(v___x_170_);
lean_dec(v_a_168_);
v___x_184_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_eToInt_166_, v___y_156_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; uint8_t v___x_186_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v___x_186_ = lean_unbox(v_a_185_);
lean_dec(v_a_185_);
if (v___x_186_ == 0)
{
lean_dec_ref(v_eToInt_166_);
goto v___jp_152_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_st_ref_get(v___y_156_);
v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v___x_187_, v_eToInt_166_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___x_187_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_188_, 1);
if (lean_obj_tag(v_a_189_) == 1)
{
lean_object* v_val_190_; 
v_val_190_ = lean_ctor_get(v_a_189_, 0);
lean_inc(v_val_190_);
lean_dec_ref_known(v_a_189_, 1);
v_val_149_ = v_val_190_;
goto v___jp_148_;
}
else
{
lean_dec(v_a_189_);
goto v___jp_152_;
}
}
else
{
return v___x_188_;
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref(v_eToInt_166_);
v_a_191_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_184_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_184_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_eToInt_166_);
v_a_200_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_167_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_167_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_dec(v___x_164_);
goto v___jp_152_;
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_e_136_);
v_a_208_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_161_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_161_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f___boxed(lean_object* v_e_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_e_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
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
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(lean_object* v_00_u03b2_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_x_304_, v_x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___boxed(lean_object* v_00_u03b2_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(v_00_u03b2_307_, v_x_308_, v_x_309_);
lean_dec_ref(v_x_309_);
lean_dec_ref(v_x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2(lean_object* v_as_311_, lean_object* v_as_x27_312_, lean_object* v_b_313_, lean_object* v_a_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___redArg(v_as_x27_312_, v_b_313_, v___y_315_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2___boxed(lean_object* v_as_327_, lean_object* v_as_x27_328_, lean_object* v_b_329_, lean_object* v_a_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__2(v_as_327_, v_as_x27_328_, v_b_329_, v_a_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec(v___y_331_);
lean_dec(v_as_x27_328_);
lean_dec(v_as_327_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0(lean_object* v_00_u03b2_343_, lean_object* v_x_344_, size_t v_x_345_, lean_object* v_x_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___redArg(v_x_344_, v_x_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
size_t v_x_52694__boxed_352_; lean_object* v_res_353_; 
v_x_52694__boxed_352_ = lean_unbox_usize(v_x_350_);
lean_dec(v_x_350_);
v_res_353_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0(v_00_u03b2_348_, v_x_349_, v_x_52694__boxed_352_, v_x_351_);
lean_dec_ref(v_x_351_);
lean_dec_ref(v_x_349_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_354_, lean_object* v_keys_355_, lean_object* v_vals_356_, lean_object* v_heq_357_, lean_object* v_i_358_, lean_object* v_k_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___redArg(v_keys_355_, v_vals_356_, v_i_358_, v_k_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_361_, lean_object* v_keys_362_, lean_object* v_vals_363_, lean_object* v_heq_364_, lean_object* v_i_365_, lean_object* v_k_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0_spec__0_spec__2(v_00_u03b2_361_, v_keys_362_, v_vals_363_, v_heq_364_, v_i_365_, v_k_366_);
lean_dec_ref(v_k_366_);
lean_dec_ref(v_vals_363_);
lean_dec_ref(v_keys_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_376_ = l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(v___x_375_, v_e_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg___boxed(lean_object* v_e_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(v_e_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(lean_object* v_e_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(v_e_385_, v_a_386_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed(lean_object* v_e_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(v_e_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec(v_a_399_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(lean_object* v_e_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = l_Lean_Expr_cleanupAnnotations(v_e_426_);
v___x_437_ = l_Lean_Expr_isApp(v___x_436_);
if (v___x_437_ == 0)
{
lean_dec_ref(v___x_436_);
goto v___jp_432_;
}
else
{
lean_object* v_arg_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_arg_438_ = lean_ctor_get(v___x_436_, 1);
lean_inc_ref(v_arg_438_);
v___x_439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_436_);
v___x_440_ = l_Lean_Expr_isApp(v___x_439_);
if (v___x_440_ == 0)
{
lean_dec_ref(v___x_439_);
lean_dec_ref(v_arg_438_);
goto v___jp_432_;
}
else
{
lean_object* v_arg_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_arg_441_ = lean_ctor_get(v___x_439_, 1);
lean_inc_ref(v_arg_441_);
v___x_442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_439_);
v___x_443_ = l_Lean_Expr_isApp(v___x_442_);
if (v___x_443_ == 0)
{
lean_dec_ref(v___x_442_);
lean_dec_ref(v_arg_441_);
lean_dec_ref(v_arg_438_);
goto v___jp_432_;
}
else
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = l_Lean_Expr_appFnCleanup___redArg(v___x_442_);
v___x_445_ = l_Lean_Expr_isApp(v___x_444_);
if (v___x_445_ == 0)
{
lean_dec_ref(v___x_444_);
lean_dec_ref(v_arg_441_);
lean_dec_ref(v_arg_438_);
goto v___jp_432_;
}
else
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = l_Lean_Expr_appFnCleanup___redArg(v___x_444_);
v___x_447_ = l_Lean_Expr_isApp(v___x_446_);
if (v___x_447_ == 0)
{
lean_dec_ref(v___x_446_);
lean_dec_ref(v_arg_441_);
lean_dec_ref(v_arg_438_);
goto v___jp_432_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v_b_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; 
v___x_448_ = l_Lean_Expr_appFnCleanup___redArg(v___x_446_);
v___x_449_ = l_Lean_Expr_isApp(v___x_448_);
if (v___x_449_ == 0)
{
lean_dec_ref(v___x_448_);
lean_dec_ref(v_arg_441_);
lean_dec_ref(v_arg_438_);
goto v___jp_432_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = l_Lean_Expr_appFnCleanup___redArg(v___x_448_);
v___x_480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2));
v___x_481_ = l_Lean_Expr_isConstOf(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5));
v___x_483_ = l_Lean_Expr_isConstOf(v___x_479_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___y_487_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8));
v___x_485_ = l_Lean_Expr_isConstOf(v___x_479_, v___x_484_);
lean_dec_ref(v___x_479_);
if (v___x_485_ == 0)
{
lean_dec_ref(v_arg_441_);
lean_dec_ref(v_arg_438_);
goto v___jp_432_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Meta_saveState___redArg(v_a_428_, v_a_430_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Meta_getIntValue_x3f(v_arg_441_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_dec(v_a_510_);
lean_dec_ref(v_arg_438_);
v___y_487_ = v___x_511_;
goto v___jp_486_;
}
else
{
lean_object* v_a_512_; uint8_t v___y_514_; uint8_t v___x_525_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
v___x_525_ = l_Lean_Exception_isInterrupt(v_a_512_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Exception_isRuntime(v_a_512_);
v___y_514_ = v___x_526_;
goto v___jp_513_;
}
else
{
lean_dec(v_a_512_);
v___y_514_ = v___x_525_;
goto v___jp_513_;
}
v___jp_513_:
{
if (v___y_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec_ref_known(v___x_511_, 1);
v___x_515_ = l_Lean_Meta_SavedState_restore___redArg(v_a_510_, v_a_428_, v_a_430_);
lean_dec(v_a_510_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; 
lean_dec_ref_known(v___x_515_, 1);
v___x_516_ = l_Lean_Meta_getIntValue_x3f(v_arg_438_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
v___y_487_ = v___x_516_;
goto v___jp_486_;
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_arg_438_);
v_a_517_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_515_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_dec(v_a_510_);
lean_dec_ref(v_arg_438_);
v___y_487_ = v___x_511_;
goto v___jp_486_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v_arg_441_);
lean_dec_ref(v_arg_438_);
v_a_527_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_509_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_509_);
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
v___jp_486_:
{
if (lean_obj_tag(v___y_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_500_; 
v_a_488_ = lean_ctor_get(v___y_487_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___y_487_);
if (v_isSharedCheck_500_ == 0)
{
v___x_490_ = v___y_487_;
v_isShared_491_ = v_isSharedCheck_500_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___y_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_500_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
if (lean_obj_tag(v_a_488_) == 0)
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_box(v___x_485_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_498_; 
lean_dec_ref_known(v_a_488_, 1);
v___x_496_ = lean_box(v___x_483_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_496_);
v___x_498_ = v___x_490_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_a_501_ = lean_ctor_get(v___y_487_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___y_487_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___y_487_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___y_487_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_479_);
lean_dec_ref(v_arg_441_);
v_b_451_ = v_arg_438_;
v___y_452_ = v_a_427_;
v___y_453_ = v_a_428_;
v___y_454_ = v_a_429_;
v___y_455_ = v_a_430_;
goto v___jp_450_;
}
}
else
{
lean_dec_ref(v___x_479_);
lean_dec_ref(v_arg_441_);
v_b_451_ = v_arg_438_;
v___y_452_ = v_a_427_;
v___y_453_ = v_a_428_;
v___y_454_ = v_a_429_;
v___y_455_ = v_a_430_;
goto v___jp_450_;
}
}
v___jp_450_:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_getIntValue_x3f(v_b_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_470_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_470_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_470_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_470_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
if (lean_obj_tag(v_a_457_) == 0)
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_box(v___x_449_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
else
{
uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
lean_dec_ref_known(v_a_457_, 1);
v___x_465_ = 0;
v___x_466_ = lean_box(v___x_465_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_466_);
v___x_468_ = v___x_459_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_456_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_456_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
}
}
}
v___jp_432_:
{
uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = 0;
v___x_434_ = lean_box(v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___boxed(lean_object* v_e_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object* v_e_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_542_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object* v_e_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec(v_a_556_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
uint8_t v___x_589_; 
lean_inc_ref(v_e_583_);
v___x_589_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_583_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; lean_object* v_f_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_590_ = 1;
v_f_591_ = l_Lean_Expr_getAppFn(v_e_583_);
lean_dec_ref(v_e_583_);
v___x_592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2));
v___x_593_ = l_Lean_Expr_isConstOf(v_f_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5));
v___x_595_ = l_Lean_Expr_isConstOf(v_f_591_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8));
v___x_597_ = l_Lean_Expr_isConstOf(v_f_591_, v___x_596_);
lean_dec_ref(v_f_591_);
v___x_598_ = lean_box(v___x_597_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec_ref(v_f_591_);
v___x_600_ = lean_box(v___x_590_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec_ref(v_f_591_);
v___x_602_ = lean_box(v___x_590_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
else
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_619_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_619_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = lean_unbox(v_a_605_);
lean_dec(v_a_605_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_box(v___x_589_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_614_ = 0;
v___x_615_ = lean_box(v___x_614_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_615_);
v___x_617_ = v___x_607_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___boxed(lean_object* v_e_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(v_e_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(lean_object* v_e_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(v_e_627_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed(lean_object* v_e_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(v_e_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec(v_a_641_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(lean_object* v_a_653_, lean_object* v_b_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_a_653_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_702_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_702_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_702_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_702_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
if (lean_obj_tag(v_a_667_) == 1)
{
lean_object* v_val_671_; lean_object* v___x_672_; 
lean_del_object(v___x_669_);
v_val_671_ = lean_ctor_get(v_a_667_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_a_667_, 1);
v___x_672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_b_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_688_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_688_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_688_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_688_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
if (lean_obj_tag(v_a_673_) == 1)
{
lean_object* v_val_677_; uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v_val_677_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_a_673_, 1);
v___x_678_ = l_instDecidableEqRat_decEq(v_val_671_, v_val_677_);
lean_dec(v_val_677_);
lean_dec(v_val_671_);
v___x_679_ = lean_box(v___x_678_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_679_);
v___x_681_ = v___x_675_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
lean_dec(v_a_673_);
lean_dec(v_val_671_);
v___x_683_ = 0;
v___x_684_ = lean_box(v___x_683_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_684_);
v___x_686_ = v___x_675_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_val_671_);
v_a_689_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_672_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_672_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
lean_dec(v_a_667_);
lean_dec_ref(v_b_654_);
v___x_697_ = 0;
v___x_698_ = lean_box(v___x_697_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_698_);
v___x_700_ = v___x_669_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v_b_654_);
v_a_703_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_666_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_666_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed(lean_object* v_a_711_, lean_object* v_b_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(v_a_711_, v_b_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_a_713_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc(lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3));
v___x_744_ = l_Lean_Meta_Grind_mbtc(v___x_743_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed(lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Meta_Grind_Arith_Cutsat_mbtc(v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec(v_a_745_);
return v_res_756_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
}
#ifdef __cplusplus
}
#endif
