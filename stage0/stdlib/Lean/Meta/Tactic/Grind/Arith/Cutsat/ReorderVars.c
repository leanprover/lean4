// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.ReorderVars
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Array_range(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Int_Linear_instBEqPoly_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reorder"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value),LEAN_SCALAR_PTR_LITERAL(236, 159, 191, 181, 87, 7, 198, 44)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "old2new: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "new2old: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(lean_object* v_a_5_, lean_object* v_x_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_9_ = lean_box(0);
v___x_14_ = lean_array_get_size(v_a_7_);
v___x_15_ = lean_nat_dec_lt(v_x_6_, v___x_14_);
if (v___x_15_ == 0)
{
lean_dec(v_a_5_);
v___y_11_ = v_a_7_;
goto v___jp_10_;
}
else
{
lean_object* v_v_16_; lean_object* v_maxLowerCoeff_17_; lean_object* v_xs_x27_18_; lean_object* v___y_20_; uint8_t v___x_32_; 
v_v_16_ = lean_array_fget(v_a_7_, v_x_6_);
v_maxLowerCoeff_17_ = lean_ctor_get(v_v_16_, 0);
v_xs_x27_18_ = lean_array_fset(v_a_7_, v_x_6_, v___x_9_);
v___x_32_ = lean_nat_dec_le(v_a_5_, v_maxLowerCoeff_17_);
if (v___x_32_ == 0)
{
v___y_20_ = v_a_5_;
goto v___jp_19_;
}
else
{
lean_dec(v_a_5_);
lean_inc(v_maxLowerCoeff_17_);
v___y_20_ = v_maxLowerCoeff_17_;
goto v___jp_19_;
}
v___jp_19_:
{
lean_object* v_maxUpperCoeff_21_; lean_object* v_maxDvdCoeff_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
v_maxUpperCoeff_21_ = lean_ctor_get(v_v_16_, 1);
v_maxDvdCoeff_22_ = lean_ctor_get(v_v_16_, 2);
v_isSharedCheck_30_ = !lean_is_exclusive(v_v_16_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; 
v_unused_31_ = lean_ctor_get(v_v_16_, 0);
lean_dec(v_unused_31_);
v___x_24_ = v_v_16_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_maxDvdCoeff_22_);
lean_inc(v_maxUpperCoeff_21_);
lean_dec(v_v_16_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___y_20_);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___y_20_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_maxUpperCoeff_21_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v_maxDvdCoeff_22_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_array_fset(v_xs_x27_18_, v_x_6_, v___x_27_);
v___y_11_ = v___x_28_;
goto v___jp_10_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_9_);
lean_ctor_set(v___x_12_, 1, v___y_11_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object* v_a_33_, lean_object* v_x_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_33_, v_x_34_, v_a_35_);
lean_dec(v_x_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object* v_a_38_, lean_object* v_x_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_38_, v_x_39_, v_a_40_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object* v_a_53_, lean_object* v_x_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(v_a_53_, v_x_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec(v_a_56_);
lean_dec(v_x_54_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object* v_a_68_, lean_object* v_x_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___y_74_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_72_ = lean_box(0);
v___x_77_ = lean_array_get_size(v_a_70_);
v___x_78_ = lean_nat_dec_lt(v_x_69_, v___x_77_);
if (v___x_78_ == 0)
{
lean_dec(v_a_68_);
v___y_74_ = v_a_70_;
goto v___jp_73_;
}
else
{
lean_object* v_v_79_; lean_object* v_maxLowerCoeff_80_; lean_object* v_maxUpperCoeff_81_; lean_object* v_maxDvdCoeff_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_94_; 
v_v_79_ = lean_array_fget(v_a_70_, v_x_69_);
v_maxLowerCoeff_80_ = lean_ctor_get(v_v_79_, 0);
v_maxUpperCoeff_81_ = lean_ctor_get(v_v_79_, 1);
v_maxDvdCoeff_82_ = lean_ctor_get(v_v_79_, 2);
v_isSharedCheck_94_ = !lean_is_exclusive(v_v_79_);
if (v_isSharedCheck_94_ == 0)
{
v___x_84_ = v_v_79_;
v_isShared_85_ = v_isSharedCheck_94_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_maxDvdCoeff_82_);
lean_inc(v_maxUpperCoeff_81_);
lean_inc(v_maxLowerCoeff_80_);
lean_dec(v_v_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_94_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_xs_x27_86_; lean_object* v___y_88_; uint8_t v___x_93_; 
v_xs_x27_86_ = lean_array_fset(v_a_70_, v_x_69_, v___x_72_);
v___x_93_ = lean_nat_dec_le(v_a_68_, v_maxUpperCoeff_81_);
if (v___x_93_ == 0)
{
lean_dec(v_maxUpperCoeff_81_);
v___y_88_ = v_a_68_;
goto v___jp_87_;
}
else
{
lean_dec(v_a_68_);
v___y_88_ = v_maxUpperCoeff_81_;
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___y_88_);
v___x_90_ = v___x_84_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_maxLowerCoeff_80_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___y_88_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v_maxDvdCoeff_82_);
v___x_90_ = v_reuseFailAlloc_92_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; 
v___x_91_ = lean_array_fset(v_xs_x27_86_, v_x_69_, v___x_90_);
v___y_74_ = v___x_91_;
goto v___jp_73_;
}
}
}
}
v___jp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_72_);
lean_ctor_set(v___x_75_, 1, v___y_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object* v_a_95_, lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_95_, v_x_96_, v_a_97_);
lean_dec(v_x_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object* v_a_100_, lean_object* v_x_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_100_, v_x_101_, v_a_102_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object* v_a_115_, lean_object* v_x_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_115_, v_x_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec(v_a_118_);
lean_dec(v_x_116_);
return v_res_129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object* v_a_132_, lean_object* v_x_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0);
v___x_137_ = lean_int_dec_lt(v_a_132_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_nat_abs(v_a_132_);
v___x_139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v___x_138_, v_x_133_, v_a_134_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_nat_abs(v_a_132_);
v___x_141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v___x_140_, v_x_133_, v_a_134_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object* v_a_142_, lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_142_, v_x_143_, v_a_144_);
lean_dec(v_x_143_);
lean_dec(v_a_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object* v_a_147_, lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_147_, v_x_148_, v_a_149_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object* v_a_162_, lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_162_, v_x_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec(v_a_165_);
lean_dec(v_x_163_);
lean_dec(v_a_162_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object* v_a_177_, lean_object* v_x_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___y_183_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_181_ = lean_box(0);
v___x_186_ = lean_array_get_size(v_a_179_);
v___x_187_ = lean_nat_dec_lt(v_x_178_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec(v_a_177_);
v___y_183_ = v_a_179_;
goto v___jp_182_;
}
else
{
lean_object* v_v_188_; lean_object* v_maxLowerCoeff_189_; lean_object* v_maxUpperCoeff_190_; lean_object* v_maxDvdCoeff_191_; lean_object* v_xs_x27_192_; uint8_t v___x_193_; 
v_v_188_ = lean_array_fget(v_a_179_, v_x_178_);
v_maxLowerCoeff_189_ = lean_ctor_get(v_v_188_, 0);
v_maxUpperCoeff_190_ = lean_ctor_get(v_v_188_, 1);
v_maxDvdCoeff_191_ = lean_ctor_get(v_v_188_, 2);
v_xs_x27_192_ = lean_array_fset(v_a_179_, v_x_178_, v___x_181_);
v___x_193_ = lean_nat_dec_le(v_a_177_, v_maxDvdCoeff_191_);
if (v___x_193_ == 0)
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_201_; 
lean_inc(v_maxUpperCoeff_190_);
lean_inc(v_maxLowerCoeff_189_);
v_isSharedCheck_201_ = !lean_is_exclusive(v_v_188_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_202_ = lean_ctor_get(v_v_188_, 2);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_v_188_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_v_188_, 0);
lean_dec(v_unused_204_);
v___x_195_ = v_v_188_;
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_v_188_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 2, v_a_177_);
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_maxLowerCoeff_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_maxUpperCoeff_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_a_177_);
v___x_198_ = v_reuseFailAlloc_200_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; 
v___x_199_ = lean_array_fset(v_xs_x27_192_, v_x_178_, v___x_198_);
v___y_183_ = v___x_199_;
goto v___jp_182_;
}
}
}
else
{
lean_object* v___x_205_; 
lean_dec(v_a_177_);
v___x_205_ = lean_array_fset(v_xs_x27_192_, v_x_178_, v_v_188_);
v___y_183_ = v___x_205_;
goto v___jp_182_;
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v___y_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object* v_a_206_, lean_object* v_x_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_206_, v_x_207_, v_a_208_);
lean_dec(v_x_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object* v_a_211_, lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_211_, v_x_212_, v_a_213_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object* v_a_226_, lean_object* v_x_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_226_, v_x_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec(v_a_229_);
lean_dec(v_x_227_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_252_; 
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_241_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_a_241_, 0);
lean_dec(v_unused_253_);
v___x_245_ = v_a_241_;
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_a_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_242_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_248_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_object* v_k_254_; lean_object* v_v_255_; lean_object* v_p_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v_snd_259_; 
v_k_254_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_k_254_);
v_v_255_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_v_255_);
v_p_256_ = lean_ctor_get(v_a_241_, 2);
lean_inc_ref(v_p_256_);
lean_dec_ref(v_a_241_);
v___x_257_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_k_254_, v_v_255_, v_a_242_);
lean_dec(v_v_255_);
lean_dec(v_k_254_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref(v___x_257_);
v_snd_259_ = lean_ctor_get(v_a_258_, 1);
lean_inc(v_snd_259_);
lean_dec(v_a_258_);
v_a_241_ = v_p_256_;
v_a_242_ = v_snd_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_261_, v_a_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_265_, v_a_266_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec(v_a_281_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object* v_as_296_, size_t v_sz_297_, size_t v_i_298_, lean_object* v_b_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_lt(v_i_298_, v_sz_297_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_b_299_);
lean_ctor_set(v___x_303_, 1, v___y_300_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_a_305_; lean_object* v_p_306_; lean_object* v___x_307_; 
lean_dec_ref(v_b_299_);
v_a_305_ = lean_array_uget_borrowed(v_as_296_, v_i_298_);
v_p_306_ = lean_ctor_get(v_a_305_, 0);
lean_inc_ref(v_p_306_);
v___x_307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_306_, v___y_300_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_snd_309_; lean_object* v___x_310_; size_t v___x_311_; size_t v___x_312_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_307_);
v_snd_309_ = lean_ctor_get(v_a_308_, 1);
lean_inc(v_snd_309_);
lean_dec(v_a_308_);
v___x_310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_add(v_i_298_, v___x_311_);
v_i_298_ = v___x_312_;
v_b_299_ = v___x_310_;
v___y_300_ = v_snd_309_;
goto _start;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_307_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_307_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_322_, lean_object* v_sz_323_, lean_object* v_i_324_, lean_object* v_b_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
size_t v_sz_boxed_328_; size_t v_i_boxed_329_; lean_object* v_res_330_; 
v_sz_boxed_328_ = lean_unbox_usize(v_sz_323_);
lean_dec(v_sz_323_);
v_i_boxed_329_ = lean_unbox_usize(v_i_324_);
lean_dec(v_i_324_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_322_, v_sz_boxed_328_, v_i_boxed_329_, v_b_325_, v___y_326_);
lean_dec_ref(v_as_322_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object* v_as_331_, size_t v_sz_332_, size_t v_i_333_, lean_object* v_b_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_333_, v_sz_332_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_b_334_);
lean_ctor_set(v___x_348_, 1, v___y_335_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v_p_351_; lean_object* v___x_352_; 
lean_dec_ref(v_b_334_);
v_a_350_ = lean_array_uget_borrowed(v_as_331_, v_i_333_);
v_p_351_ = lean_ctor_get(v_a_350_, 0);
lean_inc_ref(v_p_351_);
v___x_352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_351_, v___y_335_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_snd_354_; lean_object* v___x_355_; size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v___x_352_);
v_snd_354_ = lean_ctor_get(v_a_353_, 1);
lean_inc(v_snd_354_);
lean_dec(v_a_353_);
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_333_, v___x_356_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_331_, v_sz_332_, v___x_357_, v___x_355_, v_snd_354_);
return v___x_358_;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_352_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_352_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object* v_as_367_, lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_b_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_sz_boxed_383_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_384_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_367_, v_sz_boxed_383_, v_i_boxed_384_, v_b_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v_as_367_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_389_, size_t v_sz_390_, size_t v_i_391_, lean_object* v_b_392_, lean_object* v___y_393_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_lt(v_i_391_, v_sz_390_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_b_392_);
lean_ctor_set(v___x_396_, 1, v___y_393_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v_a_398_; lean_object* v_p_399_; lean_object* v___x_400_; 
lean_dec_ref(v_b_392_);
v_a_398_ = lean_array_uget_borrowed(v_as_389_, v_i_391_);
v_p_399_ = lean_ctor_get(v_a_398_, 0);
lean_inc_ref(v_p_399_);
v___x_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_399_, v___y_393_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v_snd_402_; lean_object* v___x_403_; size_t v___x_404_; size_t v___x_405_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
v_snd_402_ = lean_ctor_get(v_a_401_, 1);
lean_inc(v_snd_402_);
lean_dec(v_a_401_);
v___x_403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_391_, v___x_404_);
v_i_391_ = v___x_405_;
v_b_392_ = v___x_403_;
v___y_393_ = v_snd_402_;
goto _start;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_400_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_400_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_415_, lean_object* v_sz_416_, lean_object* v_i_417_, lean_object* v_b_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
size_t v_sz_boxed_421_; size_t v_i_boxed_422_; lean_object* v_res_423_; 
v_sz_boxed_421_ = lean_unbox_usize(v_sz_416_);
lean_dec(v_sz_416_);
v_i_boxed_422_ = lean_unbox_usize(v_i_417_);
lean_dec(v_i_417_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_415_, v_sz_boxed_421_, v_i_boxed_422_, v_b_418_, v___y_419_);
lean_dec_ref(v_as_415_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_b_427_);
lean_ctor_set(v___x_441_, 1, v___y_428_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v_p_444_; lean_object* v___x_445_; 
lean_dec_ref(v_b_427_);
v_a_443_ = lean_array_uget_borrowed(v_as_424_, v_i_426_);
v_p_444_ = lean_ctor_get(v_a_443_, 0);
lean_inc_ref(v_p_444_);
v___x_445_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_444_, v___y_428_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v_snd_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref(v___x_445_);
v_snd_447_ = lean_ctor_get(v_a_446_, 1);
lean_inc(v_snd_447_);
lean_dec(v_a_446_);
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_426_, v___x_449_);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_424_, v_sz_425_, v___x_450_, v___x_448_, v_snd_447_);
return v___x_451_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_445_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_445_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object* v_as_460_, lean_object* v_sz_461_, lean_object* v_i_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
size_t v_sz_boxed_476_; size_t v_i_boxed_477_; lean_object* v_res_478_; 
v_sz_boxed_476_ = lean_unbox_usize(v_sz_461_);
lean_dec(v_sz_461_);
v_i_boxed_477_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_460_, v_sz_boxed_476_, v_i_boxed_477_, v_b_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v_as_460_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object* v_init_479_, lean_object* v_n_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
if (lean_obj_tag(v_n_480_) == 0)
{
lean_object* v_cs_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_548_; 
v_cs_494_ = lean_ctor_get(v_n_480_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_n_480_);
if (v_isSharedCheck_548_ == 0)
{
v___x_496_ = v_n_480_;
v_isShared_497_ = v_isSharedCheck_548_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_cs_494_);
lean_dec(v_n_480_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_548_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; size_t v_sz_500_; size_t v___x_501_; lean_object* v___x_502_; 
v___x_498_ = lean_box(0);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_b_481_);
v_sz_500_ = lean_array_size(v_cs_494_);
v___x_501_ = ((size_t)0ULL);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_479_, v_cs_494_, v_sz_500_, v___x_501_, v___x_499_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec_ref(v_cs_494_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_539_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_539_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_539_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_539_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_fst_507_; lean_object* v_fst_508_; 
v_fst_507_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_fst_507_);
v_fst_508_ = lean_ctor_get(v_fst_507_, 0);
if (lean_obj_tag(v_fst_508_) == 0)
{
lean_object* v_snd_509_; lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_523_; 
v_snd_509_ = lean_ctor_get(v_a_503_, 1);
lean_inc(v_snd_509_);
lean_dec(v_a_503_);
v_snd_510_ = lean_ctor_get(v_fst_507_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_fst_507_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_fst_507_, 0);
lean_dec(v_unused_524_);
v___x_512_ = v_fst_507_;
v_isShared_513_ = v_isSharedCheck_523_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_dec(v_fst_507_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_523_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 1);
lean_ctor_set(v___x_496_, 0, v_snd_510_);
v___x_515_ = v___x_496_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_snd_510_);
v___x_515_ = v_reuseFailAlloc_522_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_snd_509_);
lean_ctor_set(v___x_512_, 0, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_snd_509_);
v___x_517_ = v_reuseFailAlloc_521_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_517_);
v___x_519_ = v___x_505_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_536_; 
lean_inc_ref(v_fst_508_);
lean_del_object(v___x_496_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_fst_507_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; lean_object* v_unused_538_; 
v_unused_537_ = lean_ctor_get(v_fst_507_, 1);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_fst_507_, 0);
lean_dec(v_unused_538_);
v___x_526_ = v_fst_507_;
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_fst_507_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_snd_528_; lean_object* v_val_529_; lean_object* v___x_531_; 
v_snd_528_ = lean_ctor_get(v_a_503_, 1);
lean_inc(v_snd_528_);
lean_dec(v_a_503_);
v_val_529_ = lean_ctor_get(v_fst_508_, 0);
lean_inc(v_val_529_);
lean_dec_ref(v_fst_508_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_snd_528_);
lean_ctor_set(v___x_526_, 0, v_val_529_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_val_529_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_snd_528_);
v___x_531_ = v_reuseFailAlloc_535_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_531_);
v___x_533_ = v___x_505_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
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
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_496_);
v_a_540_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_502_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_502_);
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
}
else
{
lean_object* v_vs_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_603_; 
v_vs_549_ = lean_ctor_get(v_n_480_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_n_480_);
if (v_isSharedCheck_603_ == 0)
{
v___x_551_ = v_n_480_;
v_isShared_552_ = v_isSharedCheck_603_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_vs_549_);
lean_dec(v_n_480_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_603_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; size_t v_sz_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_b_481_);
v_sz_555_ = lean_array_size(v_vs_549_);
v___x_556_ = ((size_t)0ULL);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_vs_549_, v_sz_555_, v___x_556_, v___x_554_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec_ref(v_vs_549_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_594_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_594_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_594_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_594_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_fst_562_; lean_object* v_fst_563_; 
v_fst_562_ = lean_ctor_get(v_a_558_, 0);
lean_inc(v_fst_562_);
v_fst_563_ = lean_ctor_get(v_fst_562_, 0);
if (lean_obj_tag(v_fst_563_) == 0)
{
lean_object* v_snd_564_; lean_object* v_snd_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_578_; 
v_snd_564_ = lean_ctor_get(v_a_558_, 1);
lean_inc(v_snd_564_);
lean_dec(v_a_558_);
v_snd_565_ = lean_ctor_get(v_fst_562_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_fst_562_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_fst_562_, 0);
lean_dec(v_unused_579_);
v___x_567_ = v_fst_562_;
v_isShared_568_ = v_isSharedCheck_578_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_565_);
lean_dec(v_fst_562_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_578_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v_snd_565_);
v___x_570_ = v___x_551_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_snd_565_);
v___x_570_ = v_reuseFailAlloc_577_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_snd_564_);
lean_ctor_set(v___x_567_, 0, v___x_570_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_snd_564_);
v___x_572_ = v_reuseFailAlloc_576_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_572_);
v___x_574_ = v___x_560_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_591_; 
lean_inc_ref(v_fst_563_);
lean_del_object(v___x_551_);
v_isSharedCheck_591_ = !lean_is_exclusive(v_fst_562_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; lean_object* v_unused_593_; 
v_unused_592_ = lean_ctor_get(v_fst_562_, 1);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_fst_562_, 0);
lean_dec(v_unused_593_);
v___x_581_ = v_fst_562_;
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
else
{
lean_dec(v_fst_562_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_snd_583_; lean_object* v_val_584_; lean_object* v___x_586_; 
v_snd_583_ = lean_ctor_get(v_a_558_, 1);
lean_inc(v_snd_583_);
lean_dec(v_a_558_);
v_val_584_ = lean_ctor_get(v_fst_563_, 0);
lean_inc(v_val_584_);
lean_dec_ref(v_fst_563_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_snd_583_);
lean_ctor_set(v___x_581_, 0, v_val_584_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_val_584_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_snd_583_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_586_);
v___x_588_ = v___x_560_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_del_object(v___x_551_);
v_a_595_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_557_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_557_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object* v_init_604_, lean_object* v_as_605_, size_t v_sz_606_, size_t v_i_607_, lean_object* v_b_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_lt(v_i_607_, v_sz_606_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v_b_608_);
lean_ctor_set(v___x_622_, 1, v___y_609_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
else
{
lean_object* v_snd_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_674_; 
v_snd_624_ = lean_ctor_get(v_b_608_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_b_608_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v_b_608_, 0);
lean_dec(v_unused_675_);
v___x_626_ = v_b_608_;
v_isShared_627_ = v_isSharedCheck_674_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_snd_624_);
lean_dec(v_b_608_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_674_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_a_628_; lean_object* v___x_629_; 
v_a_628_ = lean_array_uget_borrowed(v_as_605_, v_i_607_);
lean_inc(v_snd_624_);
lean_inc(v_a_628_);
v___x_629_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_604_, v_a_628_, v_snd_624_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_665_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_665_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_665_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_665_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_fst_634_; 
v_fst_634_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_fst_634_);
if (lean_obj_tag(v_fst_634_) == 0)
{
lean_object* v_snd_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_649_; 
v_snd_635_ = lean_ctor_get(v_a_630_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_a_630_, 0);
lean_dec(v_unused_650_);
v___x_637_ = v_a_630_;
v_isShared_638_ = v_isSharedCheck_649_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_snd_635_);
lean_dec(v_a_630_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_649_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v_fst_634_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_snd_624_);
lean_ctor_set(v___x_637_, 0, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_snd_624_);
v___x_641_ = v_reuseFailAlloc_648_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_643_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v_snd_635_);
lean_ctor_set(v___x_626_, 0, v___x_641_);
v___x_643_ = v___x_626_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_snd_635_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_643_);
v___x_645_ = v___x_632_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
else
{
lean_object* v_snd_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_663_; 
lean_del_object(v___x_632_);
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
v_snd_651_ = lean_ctor_get(v_a_630_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_a_630_, 0);
lean_dec(v_unused_664_);
v___x_653_ = v_a_630_;
v_isShared_654_ = v_isSharedCheck_663_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_snd_651_);
lean_dec(v_a_630_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_663_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_a_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v_a_655_ = lean_ctor_get(v_fst_634_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v_fst_634_);
v___x_656_ = lean_box(0);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_a_655_);
lean_ctor_set(v___x_653_, 0, v___x_656_);
v___x_658_ = v___x_653_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_a_655_);
v___x_658_ = v_reuseFailAlloc_662_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
size_t v___x_659_; size_t v___x_660_; 
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_add(v_i_607_, v___x_659_);
v_i_607_ = v___x_660_;
v_b_608_ = v___x_658_;
v___y_609_ = v_snd_651_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
v_a_666_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_629_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_629_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_676_ = _args[0];
lean_object* v_as_677_ = _args[1];
lean_object* v_sz_678_ = _args[2];
lean_object* v_i_679_ = _args[3];
lean_object* v_b_680_ = _args[4];
lean_object* v___y_681_ = _args[5];
lean_object* v___y_682_ = _args[6];
lean_object* v___y_683_ = _args[7];
lean_object* v___y_684_ = _args[8];
lean_object* v___y_685_ = _args[9];
lean_object* v___y_686_ = _args[10];
lean_object* v___y_687_ = _args[11];
lean_object* v___y_688_ = _args[12];
lean_object* v___y_689_ = _args[13];
lean_object* v___y_690_ = _args[14];
lean_object* v___y_691_ = _args[15];
lean_object* v___y_692_ = _args[16];
_start:
{
size_t v_sz_boxed_693_; size_t v_i_boxed_694_; lean_object* v_res_695_; 
v_sz_boxed_693_ = lean_unbox_usize(v_sz_678_);
lean_dec(v_sz_678_);
v_i_boxed_694_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_676_, v_as_677_, v_sz_boxed_693_, v_i_boxed_694_, v_b_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v_as_677_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object* v_init_696_, lean_object* v_n_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_696_, v_n_697_, v_b_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object* v_t_712_, lean_object* v_init_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_b_727_; lean_object* v___y_728_; lean_object* v_root_731_; lean_object* v_tail_732_; lean_object* v___x_733_; 
v_root_731_ = lean_ctor_get(v_t_712_, 0);
lean_inc_ref(v_root_731_);
v_tail_732_ = lean_ctor_get(v_t_712_, 1);
lean_inc_ref(v_tail_732_);
lean_dec_ref(v_t_712_);
v___x_733_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_713_, v_root_731_, v_init_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v_fst_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___x_733_);
v_fst_735_ = lean_ctor_get(v_a_734_, 0);
lean_inc(v_fst_735_);
if (lean_obj_tag(v_fst_735_) == 0)
{
lean_object* v_snd_736_; lean_object* v_a_737_; 
lean_dec_ref(v_tail_732_);
v_snd_736_ = lean_ctor_get(v_a_734_, 1);
lean_inc(v_snd_736_);
lean_dec(v_a_734_);
v_a_737_ = lean_ctor_get(v_fst_735_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v_fst_735_);
v_b_727_ = v_a_737_;
v___y_728_ = v_snd_736_;
goto v___jp_726_;
}
else
{
lean_object* v_snd_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_780_; 
v_snd_738_ = lean_ctor_get(v_a_734_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v_a_734_, 0);
lean_dec(v_unused_781_);
v___x_740_ = v_a_734_;
v_isShared_741_ = v_isSharedCheck_780_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snd_738_);
lean_dec(v_a_734_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_780_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v_a_742_ = lean_ctor_get(v_fst_735_, 0);
lean_inc(v_a_742_);
lean_dec_ref(v_fst_735_);
v___x_743_ = lean_box(0);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v_a_742_);
lean_ctor_set(v___x_740_, 0, v___x_743_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_a_742_);
v___x_745_ = v_reuseFailAlloc_779_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
size_t v_sz_746_; size_t v___x_747_; lean_object* v___x_748_; 
v_sz_746_ = lean_array_size(v_tail_732_);
v___x_747_ = ((size_t)0ULL);
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_tail_732_, v_sz_746_, v___x_747_, v___x_745_, v_snd_738_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec_ref(v_tail_732_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_770_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_770_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_770_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_770_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_fst_753_; lean_object* v_fst_754_; 
v_fst_753_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_fst_753_);
v_fst_754_ = lean_ctor_get(v_fst_753_, 0);
if (lean_obj_tag(v_fst_754_) == 0)
{
lean_object* v_snd_755_; lean_object* v_snd_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_766_; 
v_snd_755_ = lean_ctor_get(v_a_749_, 1);
lean_inc(v_snd_755_);
lean_dec(v_a_749_);
v_snd_756_ = lean_ctor_get(v_fst_753_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_fst_753_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v_fst_753_, 0);
lean_dec(v_unused_767_);
v___x_758_ = v_fst_753_;
v_isShared_759_ = v_isSharedCheck_766_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snd_756_);
lean_dec(v_fst_753_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_766_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_snd_755_);
lean_ctor_set(v___x_758_, 0, v_snd_756_);
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_snd_756_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_snd_755_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_761_);
v___x_763_ = v___x_751_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_snd_768_; lean_object* v_val_769_; 
lean_inc_ref(v_fst_754_);
lean_dec(v_fst_753_);
lean_del_object(v___x_751_);
v_snd_768_ = lean_ctor_get(v_a_749_, 1);
lean_inc(v_snd_768_);
lean_dec(v_a_749_);
v_val_769_ = lean_ctor_get(v_fst_754_, 0);
lean_inc(v_val_769_);
lean_dec_ref(v_fst_754_);
v_b_727_ = v_val_769_;
v___y_728_ = v_snd_768_;
goto v___jp_726_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_a_771_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_748_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_748_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec_ref(v_tail_732_);
v_a_782_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_733_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_733_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
v___jp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_b_727_);
lean_ctor_set(v___x_729_, 1, v___y_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object* v_t_790_, lean_object* v_init_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_790_, v_init_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec(v___y_793_);
return v_res_804_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object* v_xs_805_, lean_object* v_i_806_){
_start:
{
lean_object* v_size_807_; uint8_t v___x_808_; 
v_size_807_ = lean_ctor_get(v_xs_805_, 2);
v___x_808_ = lean_nat_dec_lt(v_i_806_, v_size_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object* v_xs_809_, lean_object* v_i_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_xs_809_, v_i_810_);
lean_dec(v_i_810_);
lean_dec_ref(v_xs_809_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object* v_a_814_, lean_object* v_range_815_, lean_object* v_b_816_, lean_object* v_i_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_stop_830_; lean_object* v_step_831_; uint8_t v___x_832_; 
v_stop_830_ = lean_ctor_get(v_range_815_, 1);
v_step_831_ = lean_ctor_get(v_range_815_, 2);
v___x_832_ = lean_nat_dec_lt(v_i_817_, v_stop_830_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v_i_817_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_b_816_);
lean_ctor_set(v___x_833_, 1, v___y_818_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_i_817_, v___y_819_, v___y_827_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v_snd_839_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___x_851_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref(v___x_835_);
v___x_837_ = lean_box(0);
v___x_851_ = lean_unbox(v_a_836_);
lean_dec(v_a_836_);
if (v___x_851_ == 0)
{
lean_object* v_dvds_852_; lean_object* v_lowers_853_; lean_object* v_uppers_854_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___x_866_; lean_object* v___y_868_; uint8_t v___x_875_; 
v_dvds_852_ = lean_ctor_get(v_a_814_, 6);
v_lowers_853_ = lean_ctor_get(v_a_814_, 7);
v_uppers_854_ = lean_ctor_get(v_a_814_, 8);
v___x_866_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0);
v___x_875_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_lowers_853_, v_i_817_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
v___x_876_ = l_outOfBounds___redArg(v___x_866_);
v___y_868_ = v___x_876_;
goto v___jp_867_;
}
else
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentArray_get_x21___redArg(v___x_866_, v_lowers_853_, v_i_817_);
v___y_868_ = v___x_877_;
goto v___jp_867_;
}
v___jp_855_:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_857_, v___x_837_, v___y_856_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v_snd_860_; lean_object* v_size_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v_snd_860_ = lean_ctor_get(v_a_859_, 1);
lean_inc(v_snd_860_);
lean_dec(v_a_859_);
v_size_861_ = lean_ctor_get(v_dvds_852_, 2);
v___x_862_ = lean_box(0);
v___x_863_ = lean_nat_dec_lt(v_i_817_, v_size_861_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
v___x_864_ = l_outOfBounds___redArg(v___x_862_);
v___y_843_ = v_snd_860_;
v___y_844_ = v___x_864_;
goto v___jp_842_;
}
else
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentArray_get_x21___redArg(v___x_862_, v_dvds_852_, v_i_817_);
v___y_843_ = v_snd_860_;
v___y_844_ = v___x_865_;
goto v___jp_842_;
}
}
else
{
lean_dec(v_i_817_);
return v___x_858_;
}
}
v___jp_867_:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_868_, v___x_837_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_snd_871_; uint8_t v___x_872_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref(v___x_869_);
v_snd_871_ = lean_ctor_get(v_a_870_, 1);
lean_inc(v_snd_871_);
lean_dec(v_a_870_);
v___x_872_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_uppers_854_, v_i_817_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = l_outOfBounds___redArg(v___x_866_);
v___y_856_ = v_snd_871_;
v___y_857_ = v___x_873_;
goto v___jp_855_;
}
else
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentArray_get_x21___redArg(v___x_866_, v_uppers_854_, v_i_817_);
v___y_856_ = v_snd_871_;
v___y_857_ = v___x_874_;
goto v___jp_855_;
}
}
else
{
lean_dec(v_i_817_);
return v___x_869_;
}
}
}
else
{
v_snd_839_ = v___y_818_;
goto v___jp_838_;
}
v___jp_838_:
{
lean_object* v___x_840_; 
v___x_840_ = lean_nat_add(v_i_817_, v_step_831_);
lean_dec(v_i_817_);
v_b_816_ = v___x_837_;
v_i_817_ = v___x_840_;
v___y_818_ = v_snd_839_;
goto _start;
}
v___jp_842_:
{
if (lean_obj_tag(v___y_844_) == 1)
{
lean_object* v_val_845_; lean_object* v_d_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_a_849_; lean_object* v_snd_850_; 
v_val_845_ = lean_ctor_get(v___y_844_, 0);
lean_inc(v_val_845_);
lean_dec_ref(v___y_844_);
v_d_846_ = lean_ctor_get(v_val_845_, 0);
lean_inc(v_d_846_);
lean_dec(v_val_845_);
v___x_847_ = lean_nat_abs(v_d_846_);
lean_dec(v_d_846_);
v___x_848_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v___x_847_, v_i_817_, v___y_843_);
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref(v___x_848_);
v_snd_850_ = lean_ctor_get(v_a_849_, 1);
lean_inc(v_snd_850_);
lean_dec(v_a_849_);
v_snd_839_ = v_snd_850_;
goto v___jp_838_;
}
else
{
lean_dec(v___y_844_);
v_snd_839_ = v___y_843_;
goto v___jp_838_;
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v___y_818_);
lean_dec(v_i_817_);
v_a_878_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_835_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_835_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object* v_a_886_, lean_object* v_range_887_, lean_object* v_b_888_, lean_object* v_i_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_886_, v_range_887_, v_b_888_, v_i_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v_range_887_);
lean_dec_ref(v_a_886_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_904_, v_a_912_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v_vars_917_; lean_object* v_size_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref(v___x_915_);
v_vars_917_ = lean_ctor_get(v_a_916_, 0);
v_size_918_ = lean_ctor_get(v_vars_917_, 2);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_918_);
v___x_921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v_size_918_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
v___x_922_ = lean_box(0);
v___x_923_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_916_, v___x_921_, v___x_922_, v___x_919_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec_ref(v___x_921_);
lean_dec(v_a_916_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_940_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_940_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_940_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_940_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_snd_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_938_; 
v_snd_928_ = lean_ctor_get(v_a_924_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_a_924_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v_a_924_, 0);
lean_dec(v_unused_939_);
v___x_930_ = v_a_924_;
v_isShared_931_ = v_isSharedCheck_938_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_snd_928_);
lean_dec(v_a_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_938_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_922_);
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_snd_928_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_933_);
v___x_935_ = v___x_926_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
else
{
return v___x_923_;
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_a_903_);
v_a_941_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_915_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_915_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec(v_a_950_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object* v_a_962_, lean_object* v_range_963_, lean_object* v_b_964_, lean_object* v_i_965_, lean_object* v_hs_966_, lean_object* v_hl_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_962_, v_range_963_, v_b_964_, v_i_965_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object** _args){
lean_object* v_a_981_ = _args[0];
lean_object* v_range_982_ = _args[1];
lean_object* v_b_983_ = _args[2];
lean_object* v_i_984_ = _args[3];
lean_object* v_hs_985_ = _args[4];
lean_object* v_hl_986_ = _args[5];
lean_object* v___y_987_ = _args[6];
lean_object* v___y_988_ = _args[7];
lean_object* v___y_989_ = _args[8];
lean_object* v___y_990_ = _args[9];
lean_object* v___y_991_ = _args[10];
lean_object* v___y_992_ = _args[11];
lean_object* v___y_993_ = _args[12];
lean_object* v___y_994_ = _args[13];
lean_object* v___y_995_ = _args[14];
lean_object* v___y_996_ = _args[15];
lean_object* v___y_997_ = _args[16];
lean_object* v___y_998_ = _args[17];
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_a_981_, v_range_982_, v_b_983_, v_i_984_, v_hs_985_, v_hl_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v_range_982_);
lean_dec_ref(v_a_981_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object* v_as_1000_, size_t v_sz_1001_, size_t v_i_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_1000_, v_sz_1001_, v_i_1002_, v_b_1003_, v___y_1004_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1017_, lean_object* v_sz_1018_, lean_object* v_i_1019_, lean_object* v_b_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
size_t v_sz_boxed_1033_; size_t v_i_boxed_1034_; lean_object* v_res_1035_; 
v_sz_boxed_1033_ = lean_unbox_usize(v_sz_1018_);
lean_dec(v_sz_1018_);
v_i_boxed_1034_ = lean_unbox_usize(v_i_1019_);
lean_dec(v_i_1019_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_1017_, v_sz_boxed_1033_, v_i_boxed_1034_, v_b_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v_as_1017_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1036_, size_t v_sz_1037_, size_t v_i_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1036_, v_sz_1037_, v_i_1038_, v_b_1039_, v___y_1040_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_1053_, lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
size_t v_sz_boxed_1069_; size_t v_i_boxed_1070_; lean_object* v_res_1071_; 
v_sz_boxed_1069_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1070_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(v_as_1053_, v_sz_boxed_1069_, v_i_boxed_1070_, v_b_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v_as_1053_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1072_, v_a_1080_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v_vars_1085_; lean_object* v_size_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
v_vars_1085_ = lean_ctor_get(v_a_1084_, 0);
lean_inc_ref(v_vars_1085_);
lean_dec(v_a_1084_);
v_size_1086_ = lean_ctor_get(v_vars_1085_, 2);
lean_inc(v_size_1086_);
lean_dec_ref(v_vars_1085_);
v___x_1087_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0));
v___x_1088_ = lean_mk_array(v_size_1086_, v___x_1087_);
v___x_1089_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v___x_1088_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_snd_1094_; lean_object* v___x_1096_; 
v_snd_1094_ = lean_ctor_get(v_a_1090_, 1);
lean_inc(v_snd_1094_);
lean_dec(v_a_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v_snd_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_snd_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1089_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1089_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1083_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1083_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec(v_a_1115_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object* v_info_1127_){
_start:
{
lean_object* v_maxLowerCoeff_1128_; lean_object* v_maxUpperCoeff_1129_; lean_object* v_maxDvdCoeff_1130_; lean_object* v___y_1132_; uint8_t v___x_1134_; 
v_maxLowerCoeff_1128_ = lean_ctor_get(v_info_1127_, 0);
v_maxUpperCoeff_1129_ = lean_ctor_get(v_info_1127_, 1);
v_maxDvdCoeff_1130_ = lean_ctor_get(v_info_1127_, 2);
v___x_1134_ = lean_nat_dec_le(v_maxLowerCoeff_1128_, v_maxUpperCoeff_1129_);
if (v___x_1134_ == 0)
{
v___y_1132_ = v_maxUpperCoeff_1129_;
goto v___jp_1131_;
}
else
{
v___y_1132_ = v_maxLowerCoeff_1128_;
goto v___jp_1131_;
}
v___jp_1131_:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_le(v_maxDvdCoeff_1130_, v___y_1132_);
if (v___x_1133_ == 0)
{
lean_inc(v_maxDvdCoeff_1130_);
return v_maxDvdCoeff_1130_;
}
else
{
lean_inc(v___y_1132_);
return v___y_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object* v_info_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v_info_1135_);
lean_dec_ref(v_info_1135_);
return v_res_1136_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object* v_infos_1137_, lean_object* v_x_1138_, lean_object* v_y_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1141_ = lean_array_get_borrowed(v___x_1140_, v_infos_1137_, v_x_1138_);
v___x_1142_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1141_);
v___x_1143_ = lean_array_get_borrowed(v___x_1140_, v_infos_1137_, v_y_1139_);
v___x_1144_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1143_);
v___x_1145_ = lean_nat_dec_lt(v___x_1142_, v___x_1144_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_nat_dec_eq(v___x_1142_, v___x_1144_);
lean_dec(v___x_1144_);
lean_dec(v___x_1142_);
if (v___x_1146_ == 0)
{
uint8_t v___x_1147_; 
v___x_1147_ = 0;
return v___x_1147_;
}
else
{
uint8_t v___x_1148_; 
v___x_1148_ = 1;
return v___x_1148_;
}
}
else
{
uint8_t v___x_1149_; 
lean_dec(v___x_1144_);
lean_dec(v___x_1142_);
v___x_1149_ = 2;
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object* v_infos_1150_, lean_object* v_x_1151_, lean_object* v_y_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1150_, v_x_1151_, v_y_1152_);
lean_dec(v_y_1152_);
lean_dec(v_x_1151_);
lean_dec_ref(v_infos_1150_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object* v_info_1155_){
_start:
{
lean_object* v_maxLowerCoeff_1156_; lean_object* v_maxUpperCoeff_1157_; lean_object* v_maxDvdCoeff_1158_; lean_object* v___y_1160_; uint8_t v___x_1162_; 
v_maxLowerCoeff_1156_ = lean_ctor_get(v_info_1155_, 0);
v_maxUpperCoeff_1157_ = lean_ctor_get(v_info_1155_, 1);
v_maxDvdCoeff_1158_ = lean_ctor_get(v_info_1155_, 2);
v___x_1162_ = lean_nat_dec_le(v_maxLowerCoeff_1156_, v_maxUpperCoeff_1157_);
if (v___x_1162_ == 0)
{
v___y_1160_ = v_maxLowerCoeff_1156_;
goto v___jp_1159_;
}
else
{
v___y_1160_ = v_maxUpperCoeff_1157_;
goto v___jp_1159_;
}
v___jp_1159_:
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_le(v_maxDvdCoeff_1158_, v___y_1160_);
if (v___x_1161_ == 0)
{
lean_inc(v_maxDvdCoeff_1158_);
return v_maxDvdCoeff_1158_;
}
else
{
lean_inc(v___y_1160_);
return v___y_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object* v_info_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v_info_1163_);
lean_dec_ref(v_info_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object* v_infos_1165_, lean_object* v_x_1166_, lean_object* v_y_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1168_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1169_ = lean_array_get_borrowed(v___x_1168_, v_infos_1165_, v_x_1166_);
v___x_1170_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1169_);
v___x_1171_ = lean_array_get_borrowed(v___x_1168_, v_infos_1165_, v_y_1167_);
v___x_1172_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1171_);
v___x_1173_ = lean_nat_dec_lt(v___x_1170_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_eq(v___x_1170_, v___x_1172_);
lean_dec(v___x_1172_);
lean_dec(v___x_1170_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; 
v___x_1175_ = 0;
return v___x_1175_;
}
else
{
uint8_t v___x_1176_; 
v___x_1176_ = 1;
return v___x_1176_;
}
}
else
{
uint8_t v___x_1177_; 
lean_dec(v___x_1172_);
lean_dec(v___x_1170_);
v___x_1177_ = 2;
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object* v_infos_1178_, lean_object* v_x_1179_, lean_object* v_y_1180_){
_start:
{
uint8_t v_res_1181_; lean_object* v_r_1182_; 
v_res_1181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1178_, v_x_1179_, v_y_1180_);
lean_dec(v_y_1180_);
lean_dec(v_x_1179_);
lean_dec_ref(v_infos_1178_);
v_r_1182_ = lean_box(v_res_1181_);
return v_r_1182_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object* v_infos_1183_, lean_object* v_x_1184_, lean_object* v_y_1185_){
_start:
{
uint8_t v___y_1187_; uint8_t v___x_1192_; 
v___x_1192_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1183_, v_x_1184_, v_y_1185_);
if (v___x_1192_ == 1)
{
uint8_t v___x_1193_; 
v___x_1193_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1183_, v_x_1184_, v_y_1185_);
v___y_1187_ = v___x_1193_;
goto v___jp_1186_;
}
else
{
v___y_1187_ = v___x_1192_;
goto v___jp_1186_;
}
v___jp_1186_:
{
if (v___y_1187_ == 1)
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_nat_dec_lt(v_x_1184_, v_y_1185_);
if (v___x_1188_ == 0)
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_nat_dec_eq(v_x_1184_, v_y_1185_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = 2;
return v___x_1190_;
}
else
{
return v___y_1187_;
}
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = 0;
return v___x_1191_;
}
}
else
{
return v___y_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object* v_infos_1194_, lean_object* v_x_1195_, lean_object* v_y_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1194_, v_x_1195_, v_y_1196_);
lean_dec(v_y_1196_);
lean_dec(v_x_1195_);
lean_dec_ref(v_infos_1194_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object* v_a_1199_, lean_object* v_x_1200_, lean_object* v_y_1201_){
_start:
{
uint8_t v___x_1202_; uint8_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_a_1199_, v_x_1200_, v_y_1201_);
v___x_1203_ = 0;
v___x_1204_ = l_instDecidableEqOrdering(v___x_1202_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object* v_a_1205_, lean_object* v_x_1206_, lean_object* v_y_1207_){
_start:
{
uint8_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1205_, v_x_1206_, v_y_1207_);
lean_dec(v_y_1207_);
lean_dec(v_x_1206_);
lean_dec_ref(v_a_1205_);
v_r_1209_ = lean_box(v_res_1208_);
return v_r_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object* v_a_1210_, lean_object* v_as_1211_, lean_object* v_lo_1212_, lean_object* v_hi_1213_){
_start:
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_nat_dec_lt(v_lo_1212_, v_hi_1213_);
if (v___x_1214_ == 0)
{
lean_dec(v_lo_1212_);
lean_dec_ref(v_a_1210_);
return v_as_1211_;
}
else
{
lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v_fst_1217_; lean_object* v_snd_1218_; uint8_t v___x_1219_; 
lean_inc_ref(v_a_1210_);
v___f_1215_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1215_, 0, v_a_1210_);
lean_inc(v_lo_1212_);
v___x_1216_ = l_Array_qpartition___redArg(v_as_1211_, v___f_1215_, v_lo_1212_, v_hi_1213_);
v_fst_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_fst_1217_);
v_snd_1218_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_snd_1218_);
lean_dec_ref(v___x_1216_);
v___x_1219_ = lean_nat_dec_le(v_hi_1213_, v_fst_1217_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_inc_ref(v_a_1210_);
v___x_1220_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1210_, v_snd_1218_, v_lo_1212_, v_fst_1217_);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_fst_1217_, v___x_1221_);
lean_dec(v_fst_1217_);
v_as_1211_ = v___x_1220_;
v_lo_1212_ = v___x_1222_;
goto _start;
}
else
{
lean_dec(v_fst_1217_);
lean_dec(v_lo_1212_);
lean_dec_ref(v_a_1210_);
return v_snd_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object* v_a_1224_, lean_object* v_as_1225_, lean_object* v_lo_1226_, lean_object* v_hi_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1224_, v_as_1225_, v_lo_1226_, v_hi_1227_);
lean_dec(v_hi_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1281_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1281_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1281_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1229_, v_a_1237_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1272_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1272_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1272_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_vars_1250_; lean_object* v_size_1251_; lean_object* v___x_1252_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_vars_1250_ = lean_ctor_get(v_a_1246_, 0);
lean_inc_ref(v_vars_1250_);
lean_dec(v_a_1246_);
v_size_1251_ = lean_ctor_get(v_vars_1250_, 2);
lean_inc(v_size_1251_);
lean_dec_ref(v_vars_1250_);
v___x_1252_ = l_Array_range(v_size_1251_);
v___x_1260_ = lean_array_get_size(v___x_1252_);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_nat_dec_eq(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___y_1266_; uint8_t v___x_1268_; 
lean_del_object(v___x_1243_);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_sub(v___x_1260_, v___x_1263_);
v___x_1268_ = lean_nat_dec_le(v___x_1261_, v___x_1264_);
if (v___x_1268_ == 0)
{
lean_inc(v___x_1264_);
v___y_1266_ = v___x_1264_;
goto v___jp_1265_;
}
else
{
v___y_1266_ = v___x_1261_;
goto v___jp_1265_;
}
v___jp_1265_:
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_nat_dec_le(v___y_1266_, v___x_1264_);
if (v___x_1267_ == 0)
{
lean_dec(v___x_1264_);
lean_inc(v___y_1266_);
v___y_1254_ = v___y_1266_;
v___y_1255_ = v___y_1266_;
goto v___jp_1253_;
}
else
{
v___y_1254_ = v___y_1266_;
v___y_1255_ = v___x_1264_;
goto v___jp_1253_;
}
}
}
else
{
lean_object* v___x_1270_; 
lean_del_object(v___x_1248_);
lean_dec(v_a_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1252_);
v___x_1270_ = v___x_1243_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1252_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
v___jp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1241_, v___x_1252_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1256_);
v___x_1258_ = v___x_1248_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_del_object(v___x_1243_);
lean_dec(v_a_1241_);
v_a_1273_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1245_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1245_);
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
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1240_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1240_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec(v_a_1290_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object* v_a_1302_, lean_object* v_n_1303_, lean_object* v_as_1304_, lean_object* v_lo_1305_, lean_object* v_hi_1306_, lean_object* v_w_1307_, lean_object* v_hlo_1308_, lean_object* v_hhi_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1302_, v_as_1304_, v_lo_1305_, v_hi_1306_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object* v_a_1311_, lean_object* v_n_1312_, lean_object* v_as_1313_, lean_object* v_lo_1314_, lean_object* v_hi_1315_, lean_object* v_w_1316_, lean_object* v_hlo_1317_, lean_object* v_hhi_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(v_a_1311_, v_n_1312_, v_as_1313_, v_lo_1314_, v_hi_1315_, v_w_1316_, v_hlo_1317_, v_hhi_1318_);
lean_dec(v_hi_1315_);
lean_dec(v_n_1312_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object* v_perm_1320_, lean_object* v_range_1321_, lean_object* v_b_1322_, lean_object* v_i_1323_){
_start:
{
lean_object* v_stop_1324_; lean_object* v_step_1325_; uint8_t v___x_1326_; 
v_stop_1324_ = lean_ctor_get(v_range_1321_, 1);
v_step_1325_ = lean_ctor_get(v_range_1321_, 2);
v___x_1326_ = lean_nat_dec_lt(v_i_1323_, v_stop_1324_);
if (v___x_1326_ == 0)
{
lean_dec(v_i_1323_);
return v_b_1322_;
}
else
{
lean_object* v___x_1327_; lean_object* v_inv_1328_; lean_object* v___x_1329_; 
v___x_1327_ = lean_array_fget_borrowed(v_perm_1320_, v_i_1323_);
lean_inc(v_i_1323_);
v_inv_1328_ = lean_array_set(v_b_1322_, v___x_1327_, v_i_1323_);
v___x_1329_ = lean_nat_add(v_i_1323_, v_step_1325_);
lean_dec(v_i_1323_);
v_b_1322_ = v_inv_1328_;
v_i_1323_ = v___x_1329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object* v_perm_1331_, lean_object* v_range_1332_, lean_object* v_b_1333_, lean_object* v_i_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1331_, v_range_1332_, v_b_1333_, v_i_1334_);
lean_dec_ref(v_range_1332_);
lean_dec_ref(v_perm_1331_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object* v_perm_1336_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_inv_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1337_ = lean_array_get_size(v_perm_1336_);
v___x_1338_ = lean_unsigned_to_nat(0u);
v_inv_1339_ = lean_mk_array(v___x_1337_, v___x_1338_);
v___x_1340_ = lean_unsigned_to_nat(1u);
v___x_1341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1338_);
lean_ctor_set(v___x_1341_, 1, v___x_1337_);
lean_ctor_set(v___x_1341_, 2, v___x_1340_);
v___x_1342_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1336_, v___x_1341_, v_inv_1339_, v___x_1338_);
lean_dec_ref(v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object* v_perm_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_perm_1343_);
lean_dec_ref(v_perm_1343_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object* v_perm_1345_, lean_object* v_range_1346_, lean_object* v_b_1347_, lean_object* v_i_1348_, lean_object* v_hs_1349_, lean_object* v_hl_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1345_, v_range_1346_, v_b_1347_, v_i_1348_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object* v_perm_1352_, lean_object* v_range_1353_, lean_object* v_b_1354_, lean_object* v_i_1355_, lean_object* v_hs_1356_, lean_object* v_hl_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(v_perm_1352_, v_range_1353_, v_b_1354_, v_i_1355_, v_hs_1356_, v_hl_1357_);
lean_dec_ref(v_range_1353_);
lean_dec_ref(v_perm_1352_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder(lean_object* v_p_1359_, lean_object* v_old2new_1360_){
_start:
{
if (lean_obj_tag(v_p_1359_) == 0)
{
return v_p_1359_;
}
else
{
lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v_p_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1373_; 
v_k_1361_ = lean_ctor_get(v_p_1359_, 0);
v_v_1362_ = lean_ctor_get(v_p_1359_, 1);
v_p_1363_ = lean_ctor_get(v_p_1359_, 2);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_p_1359_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1365_ = v_p_1359_;
v_isShared_1366_ = v_isSharedCheck_1373_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_p_1363_);
lean_inc(v_v_1362_);
lean_inc(v_k_1361_);
lean_dec(v_p_1359_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1373_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_array_get_borrowed(v___x_1367_, v_old2new_1360_, v_v_1362_);
lean_dec(v_v_1362_);
v___x_1369_ = l_Int_Linear_Poly_reorder(v_p_1363_, v_old2new_1360_);
lean_inc(v___x_1368_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 2, v___x_1369_);
lean_ctor_set(v___x_1365_, 1, v___x_1368_);
v___x_1371_ = v___x_1365_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder___boxed(lean_object* v_p_1374_, lean_object* v_old2new_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Int_Linear_Poly_reorder(v_p_1374_, v_old2new_1375_);
lean_dec_ref(v_old2new_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object* v_c_1377_, lean_object* v_old2new_1378_){
_start:
{
lean_object* v_d_1379_; lean_object* v_p_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_d_1379_ = lean_ctor_get(v_c_1377_, 0);
lean_inc(v_d_1379_);
v_p_1380_ = lean_ctor_get(v_c_1377_, 1);
lean_inc_ref(v_p_1380_);
v___x_1381_ = l_Int_Linear_Poly_reorder(v_p_1380_, v_old2new_1378_);
v___x_1382_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_c_1377_);
v___x_1383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1383_, 0, v_d_1379_);
lean_ctor_set(v___x_1383_, 1, v___x_1381_);
lean_ctor_set(v___x_1383_, 2, v___x_1382_);
v___x_1384_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object* v_c_1385_, lean_object* v_old2new_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_c_1385_, v_old2new_1386_);
lean_dec_ref(v_old2new_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object* v_c_1388_, lean_object* v_old2new_1389_){
_start:
{
lean_object* v_p_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_p_1390_ = lean_ctor_get(v_c_1388_, 0);
lean_inc_ref(v_p_1390_);
v___x_1391_ = l_Int_Linear_Poly_reorder(v_p_1390_, v_old2new_1389_);
v___x_1392_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_c_1388_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object* v_c_1395_, lean_object* v_old2new_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_c_1395_, v_old2new_1396_);
lean_dec_ref(v_old2new_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object* v_c_1398_, lean_object* v_old2new_1399_){
_start:
{
lean_object* v_p_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_p_1400_ = lean_ctor_get(v_c_1398_, 0);
lean_inc_ref(v_p_1400_);
v___x_1401_ = l_Int_Linear_Poly_reorder(v_p_1400_, v_old2new_1399_);
v___x_1402_ = lean_alloc_ctor(16, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_c_1398_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object* v_c_1405_, lean_object* v_old2new_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_c_1405_, v_old2new_1406_);
lean_dec_ref(v_old2new_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object* v_c_1408_, lean_object* v_old2new_1409_){
_start:
{
lean_object* v_p_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_p_1410_ = lean_ctor_get(v_c_1408_, 0);
lean_inc_ref(v_p_1410_);
v___x_1411_ = l_Int_Linear_Poly_reorder(v_p_1410_, v_old2new_1409_);
v___x_1412_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_c_1408_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object* v_c_1415_, lean_object* v_old2new_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_c_1415_, v_old2new_1416_);
lean_dec_ref(v_old2new_1416_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object* v_new2old_1418_, lean_object* v_inst_1419_, lean_object* v_m_1420_, lean_object* v_i_1421_, lean_object* v_h_1422_, lean_object* v_____s_1423_){
_start:
{
lean_object* v_j_1424_; lean_object* v___x_1425_; lean_object* v_r_1426_; lean_object* v___x_1427_; 
v_j_1424_ = lean_array_fget_borrowed(v_new2old_1418_, v_i_1421_);
v___x_1425_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_1419_, v_m_1420_, v_j_1424_);
v_r_1426_ = l_Lean_PersistentArray_push___redArg(v_____s_1423_, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_r_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object* v_new2old_1428_, lean_object* v_inst_1429_, lean_object* v_m_1430_, lean_object* v_i_1431_, lean_object* v_h_1432_, lean_object* v_____s_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(v_new2old_1428_, v_inst_1429_, v_m_1430_, v_i_1431_, v_h_1432_, v_____s_1433_);
lean_dec(v_i_1431_);
lean_dec_ref(v_m_1430_);
lean_dec(v_inst_1429_);
lean_dec_ref(v_new2old_1428_);
return v_res_1434_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_unsigned_to_nat(32u);
v___x_1455_ = lean_mk_empty_array_with_capacity(v___x_1454_);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11(void){
_start:
{
size_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_r_1462_; 
v___x_1457_ = ((size_t)5ULL);
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_unsigned_to_nat(32u);
v___x_1460_ = lean_mk_empty_array_with_capacity(v___x_1459_);
v___x_1461_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10);
v_r_1462_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_r_1462_, 0, v___x_1461_);
lean_ctor_set(v_r_1462_, 1, v___x_1460_);
lean_ctor_set(v_r_1462_, 2, v___x_1458_);
lean_ctor_set(v_r_1462_, 3, v___x_1458_);
lean_ctor_set_usize(v_r_1462_, 4, v___x_1457_);
return v_r_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object* v_inst_1463_, lean_object* v_m_1464_, lean_object* v_new2old_1465_){
_start:
{
lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v_r_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v_new2old_1465_);
v___f_1466_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1466_, 0, v_new2old_1465_);
lean_closure_set(v___f_1466_, 1, v_inst_1463_);
lean_closure_set(v___f_1466_, 2, v_m_1464_);
v___x_1467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9));
v___x_1468_ = lean_unsigned_to_nat(0u);
v_r_1469_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11);
v___x_1470_ = lean_array_get_size(v_new2old_1465_);
lean_dec_ref(v_new2old_1465_);
v___x_1471_ = lean_unsigned_to_nat(1u);
v___x_1472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1468_);
lean_ctor_set(v___x_1472_, 1, v___x_1470_);
lean_ctor_set(v___x_1472_, 2, v___x_1471_);
v___x_1473_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_1467_, v___x_1472_, v___f_1466_, v_r_1469_, v___x_1468_, lean_box(0), lean_box(0));
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object* v_00_u03b1_1474_, lean_object* v_inst_1475_, lean_object* v_m_1476_, lean_object* v_new2old_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v_inst_1475_, v_m_1476_, v_new2old_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
lean_object* v_ks_1483_; lean_object* v_vs_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1508_; 
v_ks_1483_ = lean_ctor_get(v_x_1479_, 0);
v_vs_1484_ = lean_ctor_get(v_x_1479_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_x_1479_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1486_ = v_x_1479_;
v_isShared_1487_ = v_isSharedCheck_1508_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_vs_1484_);
lean_inc(v_ks_1483_);
lean_dec(v_x_1479_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1508_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_array_get_size(v_ks_1483_);
v___x_1489_ = lean_nat_dec_lt(v_x_1480_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_dec(v_x_1480_);
v___x_1490_ = lean_array_push(v_ks_1483_, v_x_1481_);
v___x_1491_ = lean_array_push(v_vs_1484_, v_x_1482_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1491_);
lean_ctor_set(v___x_1486_, 0, v___x_1490_);
v___x_1493_ = v___x_1486_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
else
{
lean_object* v_k_x27_1495_; uint8_t v___x_1496_; 
v_k_x27_1495_ = lean_array_fget_borrowed(v_ks_1483_, v_x_1480_);
v___x_1496_ = l_Int_Linear_instBEqPoly_beq(v_x_1481_, v_k_x27_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1498_; 
if (v_isShared_1487_ == 0)
{
v___x_1498_ = v___x_1486_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_ks_1483_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_vs_1484_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_x_1480_, v___x_1499_);
lean_dec(v_x_1480_);
v_x_1479_ = v___x_1498_;
v_x_1480_ = v___x_1500_;
goto _start;
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1503_ = lean_array_fset(v_ks_1483_, v_x_1480_, v_x_1481_);
v___x_1504_ = lean_array_fset(v_vs_1484_, v_x_1480_, v_x_1482_);
lean_dec(v_x_1480_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1504_);
lean_ctor_set(v___x_1486_, 0, v___x_1503_);
v___x_1506_ = v___x_1486_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1504_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1509_, lean_object* v_k_1510_, lean_object* v_v_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1509_, v___x_1512_, v_k_1510_, v_v_1511_);
return v___x_1513_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; 
v___x_1514_ = ((size_t)5ULL);
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_shift_left(v___x_1515_, v___x_1514_);
return v___x_1516_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; 
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0);
v___x_1519_ = lean_usize_sub(v___x_1518_, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object* v_x_1521_, size_t v_x_1522_, size_t v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v_es_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; lean_object* v_j_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v_es_1526_ = lean_ctor_get(v_x_1521_, 0);
v___x_1527_ = ((size_t)5ULL);
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1);
v___x_1530_ = lean_usize_land(v_x_1522_, v___x_1529_);
v_j_1531_ = lean_usize_to_nat(v___x_1530_);
v___x_1532_ = lean_array_get_size(v_es_1526_);
v___x_1533_ = lean_nat_dec_lt(v_j_1531_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_dec(v_j_1531_);
lean_dec(v_x_1525_);
lean_dec_ref(v_x_1524_);
return v_x_1521_;
}
else
{
lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1570_; 
lean_inc_ref(v_es_1526_);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_x_1521_, 0);
lean_dec(v_unused_1571_);
v___x_1535_ = v_x_1521_;
v_isShared_1536_ = v_isSharedCheck_1570_;
goto v_resetjp_1534_;
}
else
{
lean_dec(v_x_1521_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1570_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v_v_1537_; lean_object* v___x_1538_; lean_object* v_xs_x27_1539_; lean_object* v___y_1541_; 
v_v_1537_ = lean_array_fget(v_es_1526_, v_j_1531_);
v___x_1538_ = lean_box(0);
v_xs_x27_1539_ = lean_array_fset(v_es_1526_, v_j_1531_, v___x_1538_);
switch(lean_obj_tag(v_v_1537_))
{
case 0:
{
lean_object* v_key_1546_; lean_object* v_val_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1557_; 
v_key_1546_ = lean_ctor_get(v_v_1537_, 0);
v_val_1547_ = lean_ctor_get(v_v_1537_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_v_1537_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1549_ = v_v_1537_;
v_isShared_1550_ = v_isSharedCheck_1557_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_val_1547_);
lean_inc(v_key_1546_);
lean_dec(v_v_1537_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1557_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
uint8_t v___x_1551_; 
v___x_1551_ = l_Int_Linear_instBEqPoly_beq(v_x_1524_, v_key_1546_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_del_object(v___x_1549_);
v___x_1552_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1546_, v_val_1547_, v_x_1524_, v_x_1525_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___y_1541_ = v___x_1553_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1555_; 
lean_dec(v_val_1547_);
lean_dec(v_key_1546_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v_x_1525_);
lean_ctor_set(v___x_1549_, 0, v_x_1524_);
v___x_1555_ = v___x_1549_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_x_1524_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_x_1525_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
v___y_1541_ = v___x_1555_;
goto v___jp_1540_;
}
}
}
}
case 1:
{
lean_object* v_node_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1568_; 
v_node_1558_ = lean_ctor_get(v_v_1537_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_v_1537_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1560_ = v_v_1537_;
v_isShared_1561_ = v_isSharedCheck_1568_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_node_1558_);
lean_dec(v_v_1537_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1568_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1562_ = lean_usize_shift_right(v_x_1522_, v___x_1527_);
v___x_1563_ = lean_usize_add(v_x_1523_, v___x_1528_);
v___x_1564_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_node_1558_, v___x_1562_, v___x_1563_, v_x_1524_, v_x_1525_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1564_);
v___x_1566_ = v___x_1560_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
v___y_1541_ = v___x_1566_;
goto v___jp_1540_;
}
}
}
default: 
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_x_1524_);
lean_ctor_set(v___x_1569_, 1, v_x_1525_);
v___y_1541_ = v___x_1569_;
goto v___jp_1540_;
}
}
v___jp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_array_fset(v_xs_x27_1539_, v_j_1531_, v___y_1541_);
lean_dec(v_j_1531_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1542_);
v___x_1544_ = v___x_1535_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
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
else
{
lean_object* v_ks_1572_; lean_object* v_vs_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1593_; 
v_ks_1572_ = lean_ctor_get(v_x_1521_, 0);
v_vs_1573_ = lean_ctor_get(v_x_1521_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1575_ = v_x_1521_;
v_isShared_1576_ = v_isSharedCheck_1593_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_vs_1573_);
lean_inc(v_ks_1572_);
lean_dec(v_x_1521_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1593_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_ks_1572_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_vs_1573_);
v___x_1578_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v_newNode_1579_; uint8_t v___y_1581_; size_t v___x_1587_; uint8_t v___x_1588_; 
v_newNode_1579_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v___x_1578_, v_x_1524_, v_x_1525_);
v___x_1587_ = ((size_t)7ULL);
v___x_1588_ = lean_usize_dec_le(v___x_1587_, v_x_1523_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1589_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1579_);
v___x_1590_ = lean_unsigned_to_nat(4u);
v___x_1591_ = lean_nat_dec_lt(v___x_1589_, v___x_1590_);
lean_dec(v___x_1589_);
v___y_1581_ = v___x_1591_;
goto v___jp_1580_;
}
else
{
v___y_1581_ = v___x_1588_;
goto v___jp_1580_;
}
v___jp_1580_:
{
if (v___y_1581_ == 0)
{
lean_object* v_ks_1582_; lean_object* v_vs_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_ks_1582_ = lean_ctor_get(v_newNode_1579_, 0);
lean_inc_ref(v_ks_1582_);
v_vs_1583_ = lean_ctor_get(v_newNode_1579_, 1);
lean_inc_ref(v_vs_1583_);
lean_dec_ref(v_newNode_1579_);
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2);
v___x_1586_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_x_1523_, v_ks_1582_, v_vs_1583_, v___x_1584_, v___x_1585_);
lean_dec_ref(v_vs_1583_);
lean_dec_ref(v_ks_1582_);
return v___x_1586_;
}
else
{
return v_newNode_1579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t v_depth_1594_, lean_object* v_keys_1595_, lean_object* v_vals_1596_, lean_object* v_i_1597_, lean_object* v_entries_1598_){
_start:
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = lean_array_get_size(v_keys_1595_);
v___x_1600_ = lean_nat_dec_lt(v_i_1597_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_dec(v_i_1597_);
return v_entries_1598_;
}
else
{
lean_object* v_k_1601_; lean_object* v_v_1602_; uint64_t v___x_1603_; size_t v_h_1604_; size_t v___x_1605_; lean_object* v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; size_t v_h_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_k_1601_ = lean_array_fget_borrowed(v_keys_1595_, v_i_1597_);
v_v_1602_ = lean_array_fget_borrowed(v_vals_1596_, v_i_1597_);
v___x_1603_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_1601_);
v_h_1604_ = lean_uint64_to_usize(v___x_1603_);
v___x_1605_ = ((size_t)5ULL);
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = ((size_t)1ULL);
v___x_1608_ = lean_usize_sub(v_depth_1594_, v___x_1607_);
v___x_1609_ = lean_usize_mul(v___x_1605_, v___x_1608_);
v_h_1610_ = lean_usize_shift_right(v_h_1604_, v___x_1609_);
v___x_1611_ = lean_nat_add(v_i_1597_, v___x_1606_);
lean_dec(v_i_1597_);
lean_inc(v_v_1602_);
lean_inc(v_k_1601_);
v___x_1612_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_entries_1598_, v_h_1610_, v_depth_1594_, v_k_1601_, v_v_1602_);
v_i_1597_ = v___x_1611_;
v_entries_1598_ = v___x_1612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1614_, lean_object* v_keys_1615_, lean_object* v_vals_1616_, lean_object* v_i_1617_, lean_object* v_entries_1618_){
_start:
{
size_t v_depth_boxed_1619_; lean_object* v_res_1620_; 
v_depth_boxed_1619_ = lean_unbox_usize(v_depth_1614_);
lean_dec(v_depth_1614_);
v_res_1620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1619_, v_keys_1615_, v_vals_1616_, v_i_1617_, v_entries_1618_);
lean_dec_ref(v_vals_1616_);
lean_dec_ref(v_keys_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object* v_x_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
size_t v_x_1892__boxed_1626_; size_t v_x_1893__boxed_1627_; lean_object* v_res_1628_; 
v_x_1892__boxed_1626_ = lean_unbox_usize(v_x_1622_);
lean_dec(v_x_1622_);
v_x_1893__boxed_1627_ = lean_unbox_usize(v_x_1623_);
lean_dec(v_x_1623_);
v_res_1628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1621_, v_x_1892__boxed_1626_, v_x_1893__boxed_1627_, v_x_1624_, v_x_1625_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
uint64_t v___x_1632_; size_t v___x_1633_; size_t v___x_1634_; lean_object* v___x_1635_; 
v___x_1632_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1630_);
v___x_1633_ = lean_uint64_to_usize(v___x_1632_);
v___x_1634_ = ((size_t)1ULL);
v___x_1635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1629_, v___x_1633_, v___x_1634_, v_x_1630_, v_x_1631_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object* v_old2new_1636_, lean_object* v_x_1637_, lean_object* v_____s_1638_){
_start:
{
lean_object* v_fst_1639_; lean_object* v_snd_1640_; lean_object* v___x_1641_; lean_object* v_m_x27_1642_; lean_object* v___x_1643_; 
v_fst_1639_ = lean_ctor_get(v_x_1637_, 0);
lean_inc(v_fst_1639_);
v_snd_1640_ = lean_ctor_get(v_x_1637_, 1);
lean_inc(v_snd_1640_);
lean_dec_ref(v_x_1637_);
v___x_1641_ = l_Int_Linear_Poly_reorder(v_fst_1639_, v_old2new_1636_);
v_m_x27_1642_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_____s_1638_, v___x_1641_, v_snd_1640_);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_m_x27_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object* v_old2new_1644_, lean_object* v_x_1645_, lean_object* v_____s_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(v_old2new_1644_, v_x_1645_, v_____s_1646_);
lean_dec_ref(v_old2new_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_1648_, lean_object* v_keys_1649_, lean_object* v_vals_1650_, lean_object* v_i_1651_, lean_object* v_acc_1652_){
_start:
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = lean_array_get_size(v_keys_1649_);
v___x_1654_ = lean_nat_dec_lt(v_i_1651_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_dec(v_i_1651_);
lean_dec_ref(v_f_1648_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_acc_1652_);
return v___x_1655_;
}
else
{
lean_object* v_k_1656_; lean_object* v_v_1657_; lean_object* v___x_1658_; 
v_k_1656_ = lean_array_fget_borrowed(v_keys_1649_, v_i_1651_);
v_v_1657_ = lean_array_fget_borrowed(v_vals_1650_, v_i_1651_);
lean_inc_ref(v_f_1648_);
lean_inc(v_v_1657_);
lean_inc(v_k_1656_);
v___x_1658_ = lean_apply_3(v_f_1648_, v_acc_1652_, v_k_1656_, v_v_1657_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_dec(v_i_1651_);
lean_dec_ref(v_f_1648_);
return v___x_1658_;
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_nat_add(v_i_1651_, v___x_1660_);
lean_dec(v_i_1651_);
v_i_1651_ = v___x_1661_;
v_acc_1652_ = v_a_1659_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_1663_, lean_object* v_keys_1664_, lean_object* v_vals_1665_, lean_object* v_i_1666_, lean_object* v_acc_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1663_, v_keys_1664_, v_vals_1665_, v_i_1666_, v_acc_1667_);
lean_dec_ref(v_vals_1665_);
lean_dec_ref(v_keys_1664_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object* v_f_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_){
_start:
{
if (lean_obj_tag(v_x_1670_) == 0)
{
lean_object* v_es_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1692_; 
v_es_1672_ = lean_ctor_get(v_x_1670_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1670_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1674_ = v_x_1670_;
v_isShared_1675_ = v_isSharedCheck_1692_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_es_1672_);
lean_dec(v_x_1670_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1692_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_array_get_size(v_es_1672_);
v___x_1678_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1680_; 
lean_dec_ref(v_es_1672_);
lean_dec_ref(v_f_1669_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set_tag(v___x_1674_, 1);
lean_ctor_set(v___x_1674_, 0, v_x_1671_);
v___x_1680_ = v___x_1674_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_x_1671_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
else
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_nat_dec_le(v___x_1677_, v___x_1677_);
if (v___x_1682_ == 0)
{
if (v___x_1678_ == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v_es_1672_);
lean_dec_ref(v_f_1669_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set_tag(v___x_1674_, 1);
lean_ctor_set(v___x_1674_, 0, v_x_1671_);
v___x_1684_ = v___x_1674_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_x_1671_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
else
{
size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
lean_del_object(v___x_1674_);
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = lean_usize_of_nat(v___x_1677_);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1669_, v_es_1672_, v___x_1686_, v___x_1687_, v_x_1671_);
lean_dec_ref(v_es_1672_);
return v___x_1688_;
}
}
else
{
size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
lean_del_object(v___x_1674_);
v___x_1689_ = ((size_t)0ULL);
v___x_1690_ = lean_usize_of_nat(v___x_1677_);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1669_, v_es_1672_, v___x_1689_, v___x_1690_, v_x_1671_);
lean_dec_ref(v_es_1672_);
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_ks_1693_; lean_object* v_vs_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_ks_1693_ = lean_ctor_get(v_x_1670_, 0);
lean_inc_ref(v_ks_1693_);
v_vs_1694_ = lean_ctor_get(v_x_1670_, 1);
lean_inc_ref(v_vs_1694_);
lean_dec_ref(v_x_1670_);
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1669_, v_ks_1693_, v_vs_1694_, v___x_1695_, v_x_1671_);
lean_dec_ref(v_vs_1694_);
lean_dec_ref(v_ks_1693_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_f_1697_, lean_object* v_as_1698_, size_t v_i_1699_, size_t v_stop_1700_, lean_object* v_b_1701_){
_start:
{
lean_object* v_a_1703_; lean_object* v___y_1708_; uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_eq(v_i_1699_, v_stop_1700_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_array_uget_borrowed(v_as_1698_, v_i_1699_);
switch(lean_obj_tag(v___x_1711_))
{
case 0:
{
lean_object* v_key_1712_; lean_object* v_val_1713_; lean_object* v___x_1714_; 
v_key_1712_ = lean_ctor_get(v___x_1711_, 0);
v_val_1713_ = lean_ctor_get(v___x_1711_, 1);
lean_inc_ref(v_f_1697_);
lean_inc(v_val_1713_);
lean_inc(v_key_1712_);
v___x_1714_ = lean_apply_3(v_f_1697_, v_b_1701_, v_key_1712_, v_val_1713_);
v___y_1708_ = v___x_1714_;
goto v___jp_1707_;
}
case 1:
{
lean_object* v_node_1715_; lean_object* v___x_1716_; 
v_node_1715_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_node_1715_);
lean_inc_ref(v_f_1697_);
v___x_1716_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1697_, v_node_1715_, v_b_1701_);
v___y_1708_ = v___x_1716_;
goto v___jp_1707_;
}
default: 
{
v_a_1703_ = v_b_1701_;
goto v___jp_1702_;
}
}
}
else
{
lean_object* v___x_1717_; 
lean_dec_ref(v_f_1697_);
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_b_1701_);
return v___x_1717_;
}
v___jp_1702_:
{
size_t v___x_1704_; size_t v___x_1705_; 
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_i_1699_, v___x_1704_);
v_i_1699_ = v___x_1705_;
v_b_1701_ = v_a_1703_;
goto _start;
}
v___jp_1707_:
{
if (lean_obj_tag(v___y_1708_) == 0)
{
lean_dec_ref(v_f_1697_);
return v___y_1708_;
}
else
{
lean_object* v_a_1709_; 
v_a_1709_ = lean_ctor_get(v___y_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___y_1708_);
v_a_1703_ = v_a_1709_;
goto v___jp_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_f_1718_, lean_object* v_as_1719_, lean_object* v_i_1720_, lean_object* v_stop_1721_, lean_object* v_b_1722_){
_start:
{
size_t v_i_boxed_1723_; size_t v_stop_boxed_1724_; lean_object* v_res_1725_; 
v_i_boxed_1723_ = lean_unbox_usize(v_i_1720_);
lean_dec(v_i_1720_);
v_stop_boxed_1724_ = lean_unbox_usize(v_stop_1721_);
lean_dec(v_stop_1721_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1718_, v_as_1719_, v_i_boxed_1723_, v_stop_boxed_1724_, v_b_1722_);
lean_dec_ref(v_as_1719_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object* v_f_1726_, lean_object* v_s_1727_, lean_object* v_a_1728_, lean_object* v_b_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1728_);
lean_ctor_set(v___x_1730_, 1, v_b_1729_);
v___x_1731_ = lean_apply_2(v_f_1726_, v___x_1730_, v_s_1727_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
v_a_1740_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1731_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1731_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object* v_map_1748_, lean_object* v_init_1749_, lean_object* v_f_1750_){
_start:
{
lean_object* v___f_1751_; lean_object* v___x_1752_; lean_object* v_a_1753_; 
v___f_1751_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1751_, 0, v_f_1750_);
v___x_1752_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v___f_1751_, v_map_1748_, v_init_1749_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
return v_a_1753_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0(void){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1(void){
_start:
{
lean_object* v___x_1755_; lean_object* v_m_x27_1756_; 
v___x_1755_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0);
v_m_x27_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_m_x27_1756_, 0, v___x_1755_);
return v_m_x27_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object* v_m_1757_, lean_object* v_old2new_1758_){
_start:
{
lean_object* v___f_1759_; lean_object* v_m_x27_1760_; lean_object* v___x_1761_; 
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1759_, 0, v_old2new_1758_);
v_m_x27_1760_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
v___x_1761_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_m_1757_, v_m_x27_1760_, v___f_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object* v_00_u03b2_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_x_1763_, v_x_1764_, v_x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object* v_00_u03c3_1767_, lean_object* v_00_u03b2_1768_, lean_object* v_map_1769_, lean_object* v_init_1770_, lean_object* v_f_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1769_, v_init_1770_, v_f_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object* v_00_u03b2_1773_, lean_object* v_x_1774_, size_t v_x_1775_, size_t v_x_1776_, lean_object* v_x_1777_, lean_object* v_x_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1774_, v_x_1775_, v_x_1776_, v_x_1777_, v_x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_, lean_object* v_x_1785_){
_start:
{
size_t v_x_2249__boxed_1786_; size_t v_x_2250__boxed_1787_; lean_object* v_res_1788_; 
v_x_2249__boxed_1786_ = lean_unbox_usize(v_x_1782_);
lean_dec(v_x_1782_);
v_x_2250__boxed_1787_ = lean_unbox_usize(v_x_1783_);
lean_dec(v_x_1783_);
v_res_1788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(v_00_u03b2_1780_, v_x_1781_, v_x_2249__boxed_1786_, v_x_2250__boxed_1787_, v_x_1784_, v_x_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object* v_map_1789_, lean_object* v_f_1790_, lean_object* v_init_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1790_, v_map_1789_, v_init_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object* v_00_u03c3_1793_, lean_object* v_00_u03c3_1794_, lean_object* v_00_u03b2_1795_, lean_object* v_map_1796_, lean_object* v_f_1797_, lean_object* v_init_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1797_, v_map_1796_, v_init_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1800_, lean_object* v_n_1801_, lean_object* v_k_1802_, lean_object* v_v_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v_n_1801_, v_k_1802_, v_v_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1805_, size_t v_depth_1806_, lean_object* v_keys_1807_, lean_object* v_vals_1808_, lean_object* v_heq_1809_, lean_object* v_i_1810_, lean_object* v_entries_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_1806_, v_keys_1807_, v_vals_1808_, v_i_1810_, v_entries_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1813_, lean_object* v_depth_1814_, lean_object* v_keys_1815_, lean_object* v_vals_1816_, lean_object* v_heq_1817_, lean_object* v_i_1818_, lean_object* v_entries_1819_){
_start:
{
size_t v_depth_boxed_1820_; lean_object* v_res_1821_; 
v_depth_boxed_1820_ = lean_unbox_usize(v_depth_1814_);
lean_dec(v_depth_1814_);
v_res_1821_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(v_00_u03b2_1813_, v_depth_boxed_1820_, v_keys_1815_, v_vals_1816_, v_heq_1817_, v_i_1818_, v_entries_1819_);
lean_dec_ref(v_vals_1816_);
lean_dec_ref(v_keys_1815_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_1822_, lean_object* v_00_u03c3_1823_, lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_f_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1826_, v_x_1827_, v_x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1831_, v_x_1832_, v_x_1833_, v_x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_00_u03c3_1838_, lean_object* v_00_u03c3_1839_, lean_object* v_f_1840_, lean_object* v_as_1841_, size_t v_i_1842_, size_t v_stop_1843_, lean_object* v_b_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1840_, v_as_1841_, v_i_1842_, v_stop_1843_, v_b_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_00_u03c3_1848_, lean_object* v_00_u03c3_1849_, lean_object* v_f_1850_, lean_object* v_as_1851_, lean_object* v_i_1852_, lean_object* v_stop_1853_, lean_object* v_b_1854_){
_start:
{
size_t v_i_boxed_1855_; size_t v_stop_boxed_1856_; lean_object* v_res_1857_; 
v_i_boxed_1855_ = lean_unbox_usize(v_i_1852_);
lean_dec(v_i_1852_);
v_stop_boxed_1856_ = lean_unbox_usize(v_stop_1853_);
lean_dec(v_stop_1853_);
v_res_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_1846_, v_00_u03b2_1847_, v_00_u03c3_1848_, v_00_u03c3_1849_, v_f_1850_, v_as_1851_, v_i_boxed_1855_, v_stop_boxed_1856_, v_b_1854_);
lean_dec_ref(v_as_1851_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_1858_, lean_object* v_00_u03c3_1859_, lean_object* v_00_u03b1_1860_, lean_object* v_00_u03b2_1861_, lean_object* v_f_1862_, lean_object* v_keys_1863_, lean_object* v_vals_1864_, lean_object* v_heq_1865_, lean_object* v_i_1866_, lean_object* v_acc_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1862_, v_keys_1863_, v_vals_1864_, v_i_1866_, v_acc_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_1869_, lean_object* v_00_u03c3_1870_, lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_f_1873_, lean_object* v_keys_1874_, lean_object* v_vals_1875_, lean_object* v_heq_1876_, lean_object* v_i_1877_, lean_object* v_acc_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(v_00_u03c3_1869_, v_00_u03c3_1870_, v_00_u03b1_1871_, v_00_u03b2_1872_, v_f_1873_, v_keys_1874_, v_vals_1875_, v_heq_1876_, v_i_1877_, v_acc_1878_);
lean_dec_ref(v_vals_1875_);
lean_dec_ref(v_keys_1874_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object* v___x_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = lean_array_get_borrowed(v___x_1882_, v___x_1880_, v_x_1881_);
lean_inc(v___x_1883_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object* v___x_1884_, lean_object* v_x_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_1884_, v_x_1885_);
lean_dec(v_x_1885_);
lean_dec_ref(v___x_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(lean_object* v_f_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_apply_1(v_f_1887_, v_x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(lean_object* v_f_1890_, lean_object* v_as_1891_, lean_object* v_i_1892_, lean_object* v_acc_1893_){
_start:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = lean_array_get_size(v_as_1891_);
v___x_1895_ = lean_nat_dec_eq(v_i_1892_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1896_ = lean_array_fget_borrowed(v_as_1891_, v_i_1892_);
lean_inc(v_f_1890_);
lean_inc(v___x_1896_);
v___x_1897_ = lean_apply_1(v_f_1890_, v___x_1896_);
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = lean_nat_add(v_i_1892_, v___x_1898_);
lean_dec(v_i_1892_);
v___x_1900_ = lean_array_push(v_acc_1893_, v___x_1897_);
v_i_1892_ = v___x_1899_;
v_acc_1893_ = v___x_1900_;
goto _start;
}
else
{
lean_dec(v_i_1892_);
lean_dec(v_f_1890_);
return v_acc_1893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg___boxed(lean_object* v_f_1902_, lean_object* v_as_1903_, lean_object* v_i_1904_, lean_object* v_acc_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_1902_, v_as_1903_, v_i_1904_, v_acc_1905_);
lean_dec_ref(v_as_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(lean_object* v_f_1907_, lean_object* v_as_1908_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_array_get_size(v_as_1908_);
v___x_1911_ = lean_mk_empty_array_with_capacity(v___x_1910_);
v___x_1912_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_1907_, v_as_1908_, v___x_1909_, v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg___boxed(lean_object* v_f_1913_, lean_object* v_as_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_1913_, v_as_1914_);
lean_dec_ref(v_as_1914_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(lean_object* v_f_1916_, size_t v_sz_1917_, size_t v_i_1918_, lean_object* v_bs_1919_){
_start:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_usize_dec_lt(v_i_1918_, v_sz_1917_);
if (v___x_1920_ == 0)
{
lean_dec(v_f_1916_);
return v_bs_1919_;
}
else
{
lean_object* v_v_1921_; lean_object* v___x_1922_; lean_object* v_bs_x27_1923_; lean_object* v___y_1925_; 
v_v_1921_ = lean_array_uget(v_bs_1919_, v_i_1918_);
v___x_1922_ = lean_unsigned_to_nat(0u);
v_bs_x27_1923_ = lean_array_uset(v_bs_1919_, v_i_1918_, v___x_1922_);
switch(lean_obj_tag(v_v_1921_))
{
case 0:
{
lean_object* v_key_1930_; lean_object* v_val_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1939_; 
v_key_1930_ = lean_ctor_get(v_v_1921_, 0);
v_val_1931_ = lean_ctor_get(v_v_1921_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_v_1921_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1933_ = v_v_1921_;
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_val_1931_);
lean_inc(v_key_1930_);
lean_dec(v_v_1921_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
lean_inc(v_f_1916_);
v___x_1935_ = lean_apply_1(v_f_1916_, v_val_1931_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v___x_1935_);
v___x_1937_ = v___x_1933_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_key_1930_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
v___y_1925_ = v___x_1937_;
goto v___jp_1924_;
}
}
}
case 1:
{
lean_object* v_node_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
v_node_1940_ = lean_ctor_get(v_v_1921_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_v_1921_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1942_ = v_v_1921_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_node_1940_);
lean_dec(v_v_1921_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_inc(v_f_1916_);
v___x_1944_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_1916_, v_node_1940_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
v___y_1925_ = v___x_1946_;
goto v___jp_1924_;
}
}
}
default: 
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_box(2);
v___y_1925_ = v___x_1949_;
goto v___jp_1924_;
}
}
v___jp_1924_:
{
size_t v___x_1926_; size_t v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_add(v_i_1918_, v___x_1926_);
v___x_1928_ = lean_array_uset(v_bs_x27_1923_, v_i_1918_, v___y_1925_);
v_i_1918_ = v___x_1927_;
v_bs_1919_ = v___x_1928_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1950_, lean_object* v_n_1951_){
_start:
{
if (lean_obj_tag(v_n_1951_) == 0)
{
lean_object* v_es_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1962_; 
v_es_1952_ = lean_ctor_get(v_n_1951_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_n_1951_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1954_ = v_n_1951_;
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_es_1952_);
lean_dec(v_n_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
size_t v_sz_1956_; size_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v_sz_1956_ = lean_array_size(v_es_1952_);
v___x_1957_ = ((size_t)0ULL);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_1950_, v_sz_1956_, v___x_1957_, v_es_1952_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1958_);
v___x_1960_ = v___x_1954_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_object* v_ks_1963_; lean_object* v_vs_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_ks_1963_ = lean_ctor_get(v_n_1951_, 0);
v_vs_1964_ = lean_ctor_get(v_n_1951_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_n_1951_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1966_ = v_n_1951_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_vs_1964_);
lean_inc(v_ks_1963_);
lean_dec(v_n_1951_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_val_1968_; lean_object* v___x_1970_; 
v_val_1968_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_1950_, v_vs_1964_);
lean_dec_ref(v_vs_1964_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v_val_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_ks_1963_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_val_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg___boxed(lean_object* v_f_1973_, lean_object* v_sz_1974_, lean_object* v_i_1975_, lean_object* v_bs_1976_){
_start:
{
size_t v_sz_boxed_1977_; size_t v_i_boxed_1978_; lean_object* v_res_1979_; 
v_sz_boxed_1977_ = lean_unbox_usize(v_sz_1974_);
lean_dec(v_sz_1974_);
v_i_boxed_1978_ = lean_unbox_usize(v_i_1975_);
lean_dec(v_i_1975_);
v_res_1979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_1973_, v_sz_boxed_1977_, v_i_boxed_1978_, v_bs_1976_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(lean_object* v_pm_1980_, lean_object* v_f_1981_){
_start:
{
lean_object* v___f_1982_; lean_object* v___x_1983_; 
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1982_, 0, v_f_1981_);
v___x_1983_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v___f_1982_, v_pm_1980_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(lean_object* v___x_1984_, size_t v_sz_1985_, size_t v_i_1986_, lean_object* v_bs_1987_){
_start:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_usize_dec_lt(v_i_1986_, v_sz_1985_);
if (v___x_1988_ == 0)
{
return v_bs_1987_;
}
else
{
lean_object* v_v_1989_; lean_object* v___x_1990_; lean_object* v_bs_x27_1991_; lean_object* v___y_1993_; 
v_v_1989_ = lean_array_uget(v_bs_1987_, v_i_1986_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v_bs_x27_1991_ = lean_array_uset(v_bs_1987_, v_i_1986_, v___x_1990_);
if (lean_obj_tag(v_v_1989_) == 0)
{
v___y_1993_ = v_v_1989_;
goto v___jp_1992_;
}
else
{
lean_object* v_val_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2006_; 
v_val_1998_ = lean_ctor_get(v_v_1989_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_v_1989_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2000_ = v_v_1989_;
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_val_1998_);
lean_dec(v_v_1989_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_1998_, v___x_1984_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2002_);
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
v___y_1993_ = v___x_2004_;
goto v___jp_1992_;
}
}
}
v___jp_1992_:
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = ((size_t)1ULL);
v___x_1995_ = lean_usize_add(v_i_1986_, v___x_1994_);
v___x_1996_ = lean_array_uset(v_bs_x27_1991_, v_i_1986_, v___y_1993_);
v_i_1986_ = v___x_1995_;
v_bs_1987_ = v___x_1996_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(lean_object* v___x_2007_, lean_object* v_sz_2008_, lean_object* v_i_2009_, lean_object* v_bs_2010_){
_start:
{
size_t v_sz_boxed_2011_; size_t v_i_boxed_2012_; lean_object* v_res_2013_; 
v_sz_boxed_2011_ = lean_unbox_usize(v_sz_2008_);
lean_dec(v_sz_2008_);
v_i_boxed_2012_ = lean_unbox_usize(v_i_2009_);
lean_dec(v_i_2009_);
v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2007_, v_sz_boxed_2011_, v_i_boxed_2012_, v_bs_2010_);
lean_dec_ref(v___x_2007_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(lean_object* v___x_2014_, size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_bs_2017_){
_start:
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2018_ == 0)
{
return v_bs_2017_;
}
else
{
lean_object* v_v_2019_; lean_object* v___x_2020_; lean_object* v_bs_x27_2021_; lean_object* v___x_2022_; size_t v___x_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v_v_2019_ = lean_array_uget(v_bs_2017_, v_i_2016_);
v___x_2020_ = lean_unsigned_to_nat(0u);
v_bs_x27_2021_ = lean_array_uset(v_bs_2017_, v_i_2016_, v___x_2020_);
v___x_2022_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2014_, v_v_2019_);
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_2016_, v___x_2023_);
v___x_2025_ = lean_array_uset(v_bs_x27_2021_, v_i_2016_, v___x_2022_);
v_i_2016_ = v___x_2024_;
v_bs_2017_ = v___x_2025_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(lean_object* v___x_2027_, lean_object* v_x_2028_){
_start:
{
if (lean_obj_tag(v_x_2028_) == 0)
{
lean_object* v_cs_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_cs_2029_ = lean_ctor_get(v_x_2028_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2031_ = v_x_2028_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_cs_2029_);
lean_dec(v_x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
size_t v_sz_2033_; size_t v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v_sz_2033_ = lean_array_size(v_cs_2029_);
v___x_2034_ = ((size_t)0ULL);
v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(v___x_2027_, v_sz_2033_, v___x_2034_, v_cs_2029_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v_vs_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2050_; 
v_vs_2040_ = lean_ctor_get(v_x_2028_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2042_ = v_x_2028_;
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_vs_2040_);
lean_dec(v_x_2028_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
size_t v_sz_2044_; size_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v_sz_2044_ = lean_array_size(v_vs_2040_);
v___x_2045_ = ((size_t)0ULL);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2027_, v_sz_2044_, v___x_2045_, v_vs_2040_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2046_);
v___x_2048_ = v___x_2042_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(lean_object* v___x_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2051_, v_x_2052_);
lean_dec_ref(v___x_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16___boxed(lean_object* v___x_2054_, lean_object* v_sz_2055_, lean_object* v_i_2056_, lean_object* v_bs_2057_){
_start:
{
size_t v_sz_boxed_2058_; size_t v_i_boxed_2059_; lean_object* v_res_2060_; 
v_sz_boxed_2058_ = lean_unbox_usize(v_sz_2055_);
lean_dec(v_sz_2055_);
v_i_boxed_2059_ = lean_unbox_usize(v_i_2056_);
lean_dec(v_i_2056_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(v___x_2054_, v_sz_boxed_2058_, v_i_boxed_2059_, v_bs_2057_);
lean_dec_ref(v___x_2054_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object* v___x_2061_, lean_object* v_t_2062_){
_start:
{
lean_object* v_root_2063_; lean_object* v_tail_2064_; lean_object* v_size_2065_; size_t v_shift_2066_; lean_object* v_tailOff_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2078_; 
v_root_2063_ = lean_ctor_get(v_t_2062_, 0);
v_tail_2064_ = lean_ctor_get(v_t_2062_, 1);
v_size_2065_ = lean_ctor_get(v_t_2062_, 2);
v_shift_2066_ = lean_ctor_get_usize(v_t_2062_, 4);
v_tailOff_2067_ = lean_ctor_get(v_t_2062_, 3);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_t_2062_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2069_ = v_t_2062_;
v_isShared_2070_ = v_isSharedCheck_2078_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_tailOff_2067_);
lean_inc(v_size_2065_);
lean_inc(v_tail_2064_);
lean_inc(v_root_2063_);
lean_dec(v_t_2062_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2078_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; size_t v_sz_2072_; size_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2071_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2061_, v_root_2063_);
v_sz_2072_ = lean_array_size(v_tail_2064_);
v___x_2073_ = ((size_t)0ULL);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2061_, v_sz_2072_, v___x_2073_, v_tail_2064_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 1, v___x_2074_);
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2076_ = v___x_2069_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_size_2065_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_tailOff_2067_);
lean_ctor_set_usize(v_reuseFailAlloc_2077_, 4, v_shift_2066_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object* v___x_2079_, lean_object* v_t_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2079_, v_t_2080_);
lean_dec_ref(v___x_2079_);
return v_res_2081_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = lean_unsigned_to_nat(32u);
v___x_2083_ = lean_mk_empty_array_with_capacity(v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1(void){
_start:
{
size_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2085_ = ((size_t)5ULL);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_unsigned_to_nat(32u);
v___x_2088_ = lean_mk_empty_array_with_capacity(v___x_2087_);
v___x_2089_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0);
v___x_2090_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2088_);
lean_ctor_set(v___x_2090_, 2, v___x_2086_);
lean_ctor_set(v___x_2090_, 3, v___x_2086_);
lean_ctor_set_usize(v___x_2090_, 4, v___x_2085_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(size_t v_sz_2091_, size_t v_i_2092_, lean_object* v_bs_2093_){
_start:
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_usize_dec_lt(v_i_2092_, v_sz_2091_);
if (v___x_2094_ == 0)
{
return v_bs_2093_;
}
else
{
lean_object* v___x_2095_; lean_object* v_bs_x27_2096_; lean_object* v___x_2097_; size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v_bs_x27_2096_ = lean_array_uset(v_bs_2093_, v_i_2092_, v___x_2095_);
v___x_2097_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1);
v___x_2098_ = ((size_t)1ULL);
v___x_2099_ = lean_usize_add(v_i_2092_, v___x_2098_);
v___x_2100_ = lean_array_uset(v_bs_x27_2096_, v_i_2092_, v___x_2097_);
v_i_2092_ = v___x_2099_;
v_bs_2093_ = v___x_2100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(lean_object* v_sz_2102_, lean_object* v_i_2103_, lean_object* v_bs_2104_){
_start:
{
size_t v_sz_boxed_2105_; size_t v_i_boxed_2106_; lean_object* v_res_2107_; 
v_sz_boxed_2105_ = lean_unbox_usize(v_sz_2102_);
lean_dec(v_sz_2102_);
v_i_boxed_2106_ = lean_unbox_usize(v_i_2103_);
lean_dec(v_i_2103_);
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_boxed_2105_, v_i_boxed_2106_, v_bs_2104_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(size_t v_sz_2108_, size_t v_i_2109_, lean_object* v_bs_2110_){
_start:
{
uint8_t v___x_2111_; 
v___x_2111_ = lean_usize_dec_lt(v_i_2109_, v_sz_2108_);
if (v___x_2111_ == 0)
{
return v_bs_2110_;
}
else
{
lean_object* v_v_2112_; lean_object* v___x_2113_; lean_object* v_bs_x27_2114_; lean_object* v___x_2115_; size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v_v_2112_ = lean_array_uget(v_bs_2110_, v_i_2109_);
v___x_2113_ = lean_unsigned_to_nat(0u);
v_bs_x27_2114_ = lean_array_uset(v_bs_2110_, v_i_2109_, v___x_2113_);
v___x_2115_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_v_2112_);
v___x_2116_ = ((size_t)1ULL);
v___x_2117_ = lean_usize_add(v_i_2109_, v___x_2116_);
v___x_2118_ = lean_array_uset(v_bs_x27_2114_, v_i_2109_, v___x_2115_);
v_i_2109_ = v___x_2117_;
v_bs_2110_ = v___x_2118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object* v_x_2120_){
_start:
{
if (lean_obj_tag(v_x_2120_) == 0)
{
lean_object* v_cs_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2131_; 
v_cs_2121_ = lean_ctor_get(v_x_2120_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_x_2120_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2123_ = v_x_2120_;
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_cs_2121_);
lean_dec(v_x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
size_t v_sz_2125_; size_t v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v_sz_2125_ = lean_array_size(v_cs_2121_);
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(v_sz_2125_, v___x_2126_, v_cs_2121_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2127_);
v___x_2129_ = v___x_2123_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
lean_object* v_vs_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2142_; 
v_vs_2132_ = lean_ctor_get(v_x_2120_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_x_2120_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2134_ = v_x_2120_;
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_vs_2132_);
lean_dec(v_x_2120_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
size_t v_sz_2136_; size_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v_sz_2136_ = lean_array_size(v_vs_2132_);
v___x_2137_ = ((size_t)0ULL);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_2136_, v___x_2137_, v_vs_2132_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2138_);
v___x_2140_ = v___x_2134_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12___boxed(lean_object* v_sz_2143_, lean_object* v_i_2144_, lean_object* v_bs_2145_){
_start:
{
size_t v_sz_boxed_2146_; size_t v_i_boxed_2147_; lean_object* v_res_2148_; 
v_sz_boxed_2146_ = lean_unbox_usize(v_sz_2143_);
lean_dec(v_sz_2143_);
v_i_boxed_2147_ = lean_unbox_usize(v_i_2144_);
lean_dec(v_i_2144_);
v_res_2148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(v_sz_boxed_2146_, v_i_boxed_2147_, v_bs_2145_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object* v_t_2149_){
_start:
{
lean_object* v_root_2150_; lean_object* v_tail_2151_; lean_object* v_size_2152_; size_t v_shift_2153_; lean_object* v_tailOff_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2165_; 
v_root_2150_ = lean_ctor_get(v_t_2149_, 0);
v_tail_2151_ = lean_ctor_get(v_t_2149_, 1);
v_size_2152_ = lean_ctor_get(v_t_2149_, 2);
v_shift_2153_ = lean_ctor_get_usize(v_t_2149_, 4);
v_tailOff_2154_ = lean_ctor_get(v_t_2149_, 3);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_t_2149_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2156_ = v_t_2149_;
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_tailOff_2154_);
lean_inc(v_size_2152_);
lean_inc(v_tail_2151_);
lean_inc(v_root_2150_);
lean_dec(v_t_2149_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; size_t v_sz_2159_; size_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2158_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_root_2150_);
v_sz_2159_ = lean_array_size(v_tail_2151_);
v___x_2160_ = ((size_t)0ULL);
v___x_2161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_2159_, v___x_2160_, v_tail_2151_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___x_2161_);
lean_ctor_set(v___x_2156_, 0, v___x_2158_);
v___x_2163_ = v___x_2156_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_size_2152_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_tailOff_2154_);
lean_ctor_set_usize(v_reuseFailAlloc_2164_, 4, v_shift_2153_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_unsigned_to_nat(32u);
v___x_2167_ = lean_mk_empty_array_with_capacity(v___x_2166_);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1(void){
_start:
{
size_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2169_ = ((size_t)5ULL);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = lean_unsigned_to_nat(32u);
v___x_2172_ = lean_mk_empty_array_with_capacity(v___x_2171_);
v___x_2173_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0);
v___x_2174_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v___x_2172_);
lean_ctor_set(v___x_2174_, 2, v___x_2170_);
lean_ctor_set(v___x_2174_, 3, v___x_2170_);
lean_ctor_set_usize(v___x_2174_, 4, v___x_2169_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(size_t v_sz_2175_, size_t v_i_2176_, lean_object* v_bs_2177_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_usize_dec_lt(v_i_2176_, v_sz_2175_);
if (v___x_2178_ == 0)
{
return v_bs_2177_;
}
else
{
lean_object* v___x_2179_; lean_object* v_bs_x27_2180_; lean_object* v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v_bs_x27_2180_ = lean_array_uset(v_bs_2177_, v_i_2176_, v___x_2179_);
v___x_2181_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1);
v___x_2182_ = ((size_t)1ULL);
v___x_2183_ = lean_usize_add(v_i_2176_, v___x_2182_);
v___x_2184_ = lean_array_uset(v_bs_x27_2180_, v_i_2176_, v___x_2181_);
v_i_2176_ = v___x_2183_;
v_bs_2177_ = v___x_2184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(lean_object* v_sz_2186_, lean_object* v_i_2187_, lean_object* v_bs_2188_){
_start:
{
size_t v_sz_boxed_2189_; size_t v_i_boxed_2190_; lean_object* v_res_2191_; 
v_sz_boxed_2189_ = lean_unbox_usize(v_sz_2186_);
lean_dec(v_sz_2186_);
v_i_boxed_2190_ = lean_unbox_usize(v_i_2187_);
lean_dec(v_i_2187_);
v_res_2191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_boxed_2189_, v_i_boxed_2190_, v_bs_2188_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(size_t v_sz_2192_, size_t v_i_2193_, lean_object* v_bs_2194_){
_start:
{
uint8_t v___x_2195_; 
v___x_2195_ = lean_usize_dec_lt(v_i_2193_, v_sz_2192_);
if (v___x_2195_ == 0)
{
return v_bs_2194_;
}
else
{
lean_object* v_v_2196_; lean_object* v___x_2197_; lean_object* v_bs_x27_2198_; lean_object* v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v_v_2196_ = lean_array_uget(v_bs_2194_, v_i_2193_);
v___x_2197_ = lean_unsigned_to_nat(0u);
v_bs_x27_2198_ = lean_array_uset(v_bs_2194_, v_i_2193_, v___x_2197_);
v___x_2199_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_v_2196_);
v___x_2200_ = ((size_t)1ULL);
v___x_2201_ = lean_usize_add(v_i_2193_, v___x_2200_);
v___x_2202_ = lean_array_uset(v_bs_x27_2198_, v_i_2193_, v___x_2199_);
v_i_2193_ = v___x_2201_;
v_bs_2194_ = v___x_2202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(lean_object* v_x_2204_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 0)
{
lean_object* v_cs_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2215_; 
v_cs_2205_ = lean_ctor_get(v_x_2204_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_x_2204_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2207_ = v_x_2204_;
v_isShared_2208_ = v_isSharedCheck_2215_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_cs_2205_);
lean_dec(v_x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2215_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
size_t v_sz_2209_; size_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v_sz_2209_ = lean_array_size(v_cs_2205_);
v___x_2210_ = ((size_t)0ULL);
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(v_sz_2209_, v___x_2210_, v_cs_2205_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2211_);
v___x_2213_ = v___x_2207_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_object* v_vs_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2226_; 
v_vs_2216_ = lean_ctor_get(v_x_2204_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_x_2204_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2218_ = v_x_2204_;
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_vs_2216_);
lean_dec(v_x_2204_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v_sz_2220_ = lean_array_size(v_vs_2216_);
v___x_2221_ = ((size_t)0ULL);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_2220_, v___x_2221_, v_vs_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2222_);
v___x_2224_ = v___x_2218_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8___boxed(lean_object* v_sz_2227_, lean_object* v_i_2228_, lean_object* v_bs_2229_){
_start:
{
size_t v_sz_boxed_2230_; size_t v_i_boxed_2231_; lean_object* v_res_2232_; 
v_sz_boxed_2230_ = lean_unbox_usize(v_sz_2227_);
lean_dec(v_sz_2227_);
v_i_boxed_2231_ = lean_unbox_usize(v_i_2228_);
lean_dec(v_i_2228_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(v_sz_boxed_2230_, v_i_boxed_2231_, v_bs_2229_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object* v_t_2233_){
_start:
{
lean_object* v_root_2234_; lean_object* v_tail_2235_; lean_object* v_size_2236_; size_t v_shift_2237_; lean_object* v_tailOff_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2249_; 
v_root_2234_ = lean_ctor_get(v_t_2233_, 0);
v_tail_2235_ = lean_ctor_get(v_t_2233_, 1);
v_size_2236_ = lean_ctor_get(v_t_2233_, 2);
v_shift_2237_ = lean_ctor_get_usize(v_t_2233_, 4);
v_tailOff_2238_ = lean_ctor_get(v_t_2233_, 3);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_t_2233_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2240_ = v_t_2233_;
v_isShared_2241_ = v_isSharedCheck_2249_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_tailOff_2238_);
lean_inc(v_size_2236_);
lean_inc(v_tail_2235_);
lean_inc(v_root_2234_);
lean_dec(v_t_2233_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2249_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2242_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_root_2234_);
v_sz_2243_ = lean_array_size(v_tail_2235_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_2243_, v___x_2244_, v_tail_2235_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 1, v___x_2245_);
lean_ctor_set(v___x_2240_, 0, v___x_2242_);
v___x_2247_ = v___x_2240_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_size_2236_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_tailOff_2238_);
lean_ctor_set_usize(v_reuseFailAlloc_2248_, 4, v_shift_2237_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(size_t v_sz_2250_, size_t v_i_2251_, lean_object* v_bs_2252_){
_start:
{
uint8_t v___x_2253_; 
v___x_2253_ = lean_usize_dec_lt(v_i_2251_, v_sz_2250_);
if (v___x_2253_ == 0)
{
return v_bs_2252_;
}
else
{
lean_object* v___x_2254_; lean_object* v_bs_x27_2255_; lean_object* v___x_2256_; size_t v___x_2257_; size_t v___x_2258_; lean_object* v___x_2259_; 
v___x_2254_ = lean_unsigned_to_nat(0u);
v_bs_x27_2255_ = lean_array_uset(v_bs_2252_, v_i_2251_, v___x_2254_);
v___x_2256_ = lean_box(1);
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_add(v_i_2251_, v___x_2257_);
v___x_2259_ = lean_array_uset(v_bs_x27_2255_, v_i_2251_, v___x_2256_);
v_i_2251_ = v___x_2258_;
v_bs_2252_ = v___x_2259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(lean_object* v_sz_2261_, lean_object* v_i_2262_, lean_object* v_bs_2263_){
_start:
{
size_t v_sz_boxed_2264_; size_t v_i_boxed_2265_; lean_object* v_res_2266_; 
v_sz_boxed_2264_ = lean_unbox_usize(v_sz_2261_);
lean_dec(v_sz_2261_);
v_i_boxed_2265_ = lean_unbox_usize(v_i_2262_);
lean_dec(v_i_2262_);
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_boxed_2264_, v_i_boxed_2265_, v_bs_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(size_t v_sz_2267_, size_t v_i_2268_, lean_object* v_bs_2269_){
_start:
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_usize_dec_lt(v_i_2268_, v_sz_2267_);
if (v___x_2270_ == 0)
{
return v_bs_2269_;
}
else
{
lean_object* v_v_2271_; lean_object* v___x_2272_; lean_object* v_bs_x27_2273_; lean_object* v___x_2274_; size_t v___x_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v_v_2271_ = lean_array_uget(v_bs_2269_, v_i_2268_);
v___x_2272_ = lean_unsigned_to_nat(0u);
v_bs_x27_2273_ = lean_array_uset(v_bs_2269_, v_i_2268_, v___x_2272_);
v___x_2274_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_v_2271_);
v___x_2275_ = ((size_t)1ULL);
v___x_2276_ = lean_usize_add(v_i_2268_, v___x_2275_);
v___x_2277_ = lean_array_uset(v_bs_x27_2273_, v_i_2268_, v___x_2274_);
v_i_2268_ = v___x_2276_;
v_bs_2269_ = v___x_2277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(lean_object* v_x_2279_){
_start:
{
if (lean_obj_tag(v_x_2279_) == 0)
{
lean_object* v_cs_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2290_; 
v_cs_2280_ = lean_ctor_get(v_x_2279_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2279_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2282_ = v_x_2279_;
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_cs_2280_);
lean_dec(v_x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
size_t v_sz_2284_; size_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v_sz_2284_ = lean_array_size(v_cs_2280_);
v___x_2285_ = ((size_t)0ULL);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(v_sz_2284_, v___x_2285_, v_cs_2280_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2286_);
v___x_2288_ = v___x_2282_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
else
{
lean_object* v_vs_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2301_; 
v_vs_2291_ = lean_ctor_get(v_x_2279_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_x_2279_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2293_ = v_x_2279_;
v_isShared_2294_ = v_isSharedCheck_2301_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_vs_2291_);
lean_dec(v_x_2279_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2301_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
size_t v_sz_2295_; size_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v_sz_2295_ = lean_array_size(v_vs_2291_);
v___x_2296_ = ((size_t)0ULL);
v___x_2297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_2295_, v___x_2296_, v_vs_2291_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2297_);
v___x_2299_ = v___x_2293_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21___boxed(lean_object* v_sz_2302_, lean_object* v_i_2303_, lean_object* v_bs_2304_){
_start:
{
size_t v_sz_boxed_2305_; size_t v_i_boxed_2306_; lean_object* v_res_2307_; 
v_sz_boxed_2305_ = lean_unbox_usize(v_sz_2302_);
lean_dec(v_sz_2302_);
v_i_boxed_2306_ = lean_unbox_usize(v_i_2303_);
lean_dec(v_i_2303_);
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(v_sz_boxed_2305_, v_i_boxed_2306_, v_bs_2304_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object* v_t_2308_){
_start:
{
lean_object* v_root_2309_; lean_object* v_tail_2310_; lean_object* v_size_2311_; size_t v_shift_2312_; lean_object* v_tailOff_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2324_; 
v_root_2309_ = lean_ctor_get(v_t_2308_, 0);
v_tail_2310_ = lean_ctor_get(v_t_2308_, 1);
v_size_2311_ = lean_ctor_get(v_t_2308_, 2);
v_shift_2312_ = lean_ctor_get_usize(v_t_2308_, 4);
v_tailOff_2313_ = lean_ctor_get(v_t_2308_, 3);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_t_2308_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2315_ = v_t_2308_;
v_isShared_2316_ = v_isSharedCheck_2324_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_tailOff_2313_);
lean_inc(v_size_2311_);
lean_inc(v_tail_2310_);
lean_inc(v_root_2309_);
lean_dec(v_t_2308_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2324_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; size_t v_sz_2318_; size_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2317_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_root_2309_);
v_sz_2318_ = lean_array_size(v_tail_2310_);
v___x_2319_ = ((size_t)0ULL);
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_2318_, v___x_2319_, v_tail_2310_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v___x_2320_);
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2322_ = v___x_2315_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_size_2311_);
lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_tailOff_2313_);
lean_ctor_set_usize(v_reuseFailAlloc_2323_, 4, v_shift_2312_);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object* v___x_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
if (lean_obj_tag(v_a_2326_) == 0)
{
lean_object* v___x_2328_; 
v___x_2328_ = l_List_reverse___redArg(v_a_2327_);
return v___x_2328_;
}
else
{
lean_object* v_head_2329_; lean_object* v_tail_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2340_; 
v_head_2329_ = lean_ctor_get(v_a_2326_, 0);
v_tail_2330_ = lean_ctor_get(v_a_2326_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_a_2326_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2332_ = v_a_2326_;
v_isShared_2333_ = v_isSharedCheck_2340_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_tail_2330_);
lean_inc(v_head_2329_);
lean_dec(v_a_2326_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2340_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = lean_array_get_borrowed(v___x_2334_, v___x_2325_, v_head_2329_);
lean_dec(v_head_2329_);
lean_inc(v___x_2335_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 1, v_a_2327_);
lean_ctor_set(v___x_2332_, 0, v___x_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_a_2327_);
v___x_2337_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
v_a_2326_ = v_tail_2330_;
v_a_2327_ = v___x_2337_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object* v___x_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2341_, v_a_2342_, v_a_2343_);
lean_dec_ref(v___x_2341_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(size_t v_sz_2345_, size_t v_i_2346_, lean_object* v_bs_2347_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_usize_dec_lt(v_i_2346_, v_sz_2345_);
if (v___x_2348_ == 0)
{
return v_bs_2347_;
}
else
{
lean_object* v___x_2349_; lean_object* v_bs_x27_2350_; lean_object* v___x_2351_; size_t v___x_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = lean_unsigned_to_nat(0u);
v_bs_x27_2350_ = lean_array_uset(v_bs_2347_, v_i_2346_, v___x_2349_);
v___x_2351_ = lean_box(0);
v___x_2352_ = ((size_t)1ULL);
v___x_2353_ = lean_usize_add(v_i_2346_, v___x_2352_);
v___x_2354_ = lean_array_uset(v_bs_x27_2350_, v_i_2346_, v___x_2351_);
v_i_2346_ = v___x_2353_;
v_bs_2347_ = v___x_2354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object* v_sz_2356_, lean_object* v_i_2357_, lean_object* v_bs_2358_){
_start:
{
size_t v_sz_boxed_2359_; size_t v_i_boxed_2360_; lean_object* v_res_2361_; 
v_sz_boxed_2359_ = lean_unbox_usize(v_sz_2356_);
lean_dec(v_sz_2356_);
v_i_boxed_2360_ = lean_unbox_usize(v_i_2357_);
lean_dec(v_i_2357_);
v_res_2361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_boxed_2359_, v_i_boxed_2360_, v_bs_2358_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(size_t v_sz_2362_, size_t v_i_2363_, lean_object* v_bs_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_usize_dec_lt(v_i_2363_, v_sz_2362_);
if (v___x_2365_ == 0)
{
return v_bs_2364_;
}
else
{
lean_object* v_v_2366_; lean_object* v___x_2367_; lean_object* v_bs_x27_2368_; lean_object* v___x_2369_; size_t v___x_2370_; size_t v___x_2371_; lean_object* v___x_2372_; 
v_v_2366_ = lean_array_uget(v_bs_2364_, v_i_2363_);
v___x_2367_ = lean_unsigned_to_nat(0u);
v_bs_x27_2368_ = lean_array_uset(v_bs_2364_, v_i_2363_, v___x_2367_);
v___x_2369_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_v_2366_);
v___x_2370_ = ((size_t)1ULL);
v___x_2371_ = lean_usize_add(v_i_2363_, v___x_2370_);
v___x_2372_ = lean_array_uset(v_bs_x27_2368_, v_i_2363_, v___x_2369_);
v_i_2363_ = v___x_2371_;
v_bs_2364_ = v___x_2372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object* v_x_2374_){
_start:
{
if (lean_obj_tag(v_x_2374_) == 0)
{
lean_object* v_cs_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2385_; 
v_cs_2375_ = lean_ctor_get(v_x_2374_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_x_2374_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2377_ = v_x_2374_;
v_isShared_2378_ = v_isSharedCheck_2385_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_cs_2375_);
lean_dec(v_x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2385_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
size_t v_sz_2379_; size_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v_sz_2379_ = lean_array_size(v_cs_2375_);
v___x_2380_ = ((size_t)0ULL);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(v_sz_2379_, v___x_2380_, v_cs_2375_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2381_);
v___x_2383_ = v___x_2377_;
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
lean_object* v_vs_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2396_; 
v_vs_2386_ = lean_ctor_get(v_x_2374_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_x_2374_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2388_ = v_x_2374_;
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_vs_2386_);
lean_dec(v_x_2374_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
size_t v_sz_2390_; size_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v_sz_2390_ = lean_array_size(v_vs_2386_);
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_2390_, v___x_2391_, v_vs_2386_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2392_);
v___x_2394_ = v___x_2388_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_2397_, lean_object* v_i_2398_, lean_object* v_bs_2399_){
_start:
{
size_t v_sz_boxed_2400_; size_t v_i_boxed_2401_; lean_object* v_res_2402_; 
v_sz_boxed_2400_ = lean_unbox_usize(v_sz_2397_);
lean_dec(v_sz_2397_);
v_i_boxed_2401_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_res_2402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(v_sz_boxed_2400_, v_i_boxed_2401_, v_bs_2399_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object* v_t_2403_){
_start:
{
lean_object* v_root_2404_; lean_object* v_tail_2405_; lean_object* v_size_2406_; size_t v_shift_2407_; lean_object* v_tailOff_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2419_; 
v_root_2404_ = lean_ctor_get(v_t_2403_, 0);
v_tail_2405_ = lean_ctor_get(v_t_2403_, 1);
v_size_2406_ = lean_ctor_get(v_t_2403_, 2);
v_shift_2407_ = lean_ctor_get_usize(v_t_2403_, 4);
v_tailOff_2408_ = lean_ctor_get(v_t_2403_, 3);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_t_2403_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2410_ = v_t_2403_;
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_tailOff_2408_);
lean_inc(v_size_2406_);
lean_inc(v_tail_2405_);
lean_inc(v_root_2404_);
lean_dec(v_t_2403_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; size_t v_sz_2413_; size_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2412_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_root_2404_);
v_sz_2413_ = lean_array_size(v_tail_2405_);
v___x_2414_ = ((size_t)0ULL);
v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_2413_, v___x_2414_, v_tail_2405_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v___x_2415_);
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2417_ = v___x_2410_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_size_2406_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_tailOff_2408_);
lean_ctor_set_usize(v_reuseFailAlloc_2418_, 4, v_shift_2407_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object* v_a_2420_, lean_object* v___f_2421_, lean_object* v___x_2422_, lean_object* v_s_2423_){
_start:
{
lean_object* v_vars_2424_; lean_object* v_varMap_2425_; lean_object* v_natToIntMap_2426_; lean_object* v_natDef_2427_; lean_object* v_dvds_2428_; lean_object* v_lowers_2429_; lean_object* v_uppers_2430_; lean_object* v_diseqs_2431_; lean_object* v_elimEqs_2432_; lean_object* v_elimStack_2433_; lean_object* v_occurs_2434_; lean_object* v_assignment_2435_; lean_object* v_nextCnstrId_2436_; uint8_t v_caseSplits_2437_; lean_object* v_conflict_x3f_2438_; lean_object* v_divMod_2439_; lean_object* v_toIntIds_2440_; lean_object* v_toIntInfos_2441_; lean_object* v_toIntTermMap_2442_; lean_object* v_toIntVarMap_2443_; uint8_t v_usedCommRing_2444_; lean_object* v_nonlinearOccs_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2467_; 
v_vars_2424_ = lean_ctor_get(v_s_2423_, 0);
v_varMap_2425_ = lean_ctor_get(v_s_2423_, 1);
v_natToIntMap_2426_ = lean_ctor_get(v_s_2423_, 4);
v_natDef_2427_ = lean_ctor_get(v_s_2423_, 5);
v_dvds_2428_ = lean_ctor_get(v_s_2423_, 6);
v_lowers_2429_ = lean_ctor_get(v_s_2423_, 7);
v_uppers_2430_ = lean_ctor_get(v_s_2423_, 8);
v_diseqs_2431_ = lean_ctor_get(v_s_2423_, 9);
v_elimEqs_2432_ = lean_ctor_get(v_s_2423_, 10);
v_elimStack_2433_ = lean_ctor_get(v_s_2423_, 11);
v_occurs_2434_ = lean_ctor_get(v_s_2423_, 12);
v_assignment_2435_ = lean_ctor_get(v_s_2423_, 13);
v_nextCnstrId_2436_ = lean_ctor_get(v_s_2423_, 14);
v_caseSplits_2437_ = lean_ctor_get_uint8(v_s_2423_, sizeof(void*)*23);
v_conflict_x3f_2438_ = lean_ctor_get(v_s_2423_, 15);
v_divMod_2439_ = lean_ctor_get(v_s_2423_, 17);
v_toIntIds_2440_ = lean_ctor_get(v_s_2423_, 18);
v_toIntInfos_2441_ = lean_ctor_get(v_s_2423_, 19);
v_toIntTermMap_2442_ = lean_ctor_get(v_s_2423_, 20);
v_toIntVarMap_2443_ = lean_ctor_get(v_s_2423_, 21);
v_usedCommRing_2444_ = lean_ctor_get_uint8(v_s_2423_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2445_ = lean_ctor_get(v_s_2423_, 22);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_s_2423_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; lean_object* v_unused_2469_; lean_object* v_unused_2470_; 
v_unused_2468_ = lean_ctor_get(v_s_2423_, 16);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v_s_2423_, 3);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v_s_2423_, 2);
lean_dec(v_unused_2470_);
v___x_2447_ = v_s_2423_;
v_isShared_2448_ = v_isSharedCheck_2467_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_nonlinearOccs_2445_);
lean_inc(v_toIntVarMap_2443_);
lean_inc(v_toIntTermMap_2442_);
lean_inc(v_toIntInfos_2441_);
lean_inc(v_toIntIds_2440_);
lean_inc(v_divMod_2439_);
lean_inc(v_conflict_x3f_2438_);
lean_inc(v_nextCnstrId_2436_);
lean_inc(v_assignment_2435_);
lean_inc(v_occurs_2434_);
lean_inc(v_elimStack_2433_);
lean_inc(v_elimEqs_2432_);
lean_inc(v_diseqs_2431_);
lean_inc(v_uppers_2430_);
lean_inc(v_lowers_2429_);
lean_inc(v_dvds_2428_);
lean_inc(v_natDef_2427_);
lean_inc(v_natToIntMap_2426_);
lean_inc(v_varMap_2425_);
lean_inc(v_vars_2424_);
lean_dec(v_s_2423_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2467_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2449_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_a_2420_);
lean_inc_ref(v_vars_2424_);
v___x_2450_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2449_, v_vars_2424_, v_a_2420_);
lean_inc_ref(v___f_2421_);
lean_inc_ref(v_varMap_2425_);
v___x_2451_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_varMap_2425_, v___f_2421_);
v___x_2452_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_natDef_2427_, v___f_2421_);
v___x_2453_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(v_dvds_2428_);
v___x_2454_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_lowers_2429_);
v___x_2455_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_uppers_2430_);
v___x_2456_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_diseqs_2431_);
v___x_2457_ = lean_box(0);
v___x_2458_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2457_, v_elimEqs_2432_, v_a_2420_);
v___x_2459_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2422_, v___x_2458_);
v___x_2460_ = lean_box(0);
v___x_2461_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2422_, v_elimStack_2433_, v___x_2460_);
v___x_2462_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v_occurs_2434_);
v___x_2463_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 16, v___x_2463_);
lean_ctor_set(v___x_2447_, 12, v___x_2462_);
lean_ctor_set(v___x_2447_, 11, v___x_2461_);
lean_ctor_set(v___x_2447_, 10, v___x_2459_);
lean_ctor_set(v___x_2447_, 9, v___x_2456_);
lean_ctor_set(v___x_2447_, 8, v___x_2455_);
lean_ctor_set(v___x_2447_, 7, v___x_2454_);
lean_ctor_set(v___x_2447_, 6, v___x_2453_);
lean_ctor_set(v___x_2447_, 5, v___x_2452_);
lean_ctor_set(v___x_2447_, 3, v_varMap_2425_);
lean_ctor_set(v___x_2447_, 2, v_vars_2424_);
lean_ctor_set(v___x_2447_, 1, v___x_2451_);
lean_ctor_set(v___x_2447_, 0, v___x_2450_);
v___x_2465_ = v___x_2447_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v_vars_2424_);
lean_ctor_set(v_reuseFailAlloc_2466_, 3, v_varMap_2425_);
lean_ctor_set(v_reuseFailAlloc_2466_, 4, v_natToIntMap_2426_);
lean_ctor_set(v_reuseFailAlloc_2466_, 5, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2466_, 6, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2466_, 7, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2466_, 8, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2466_, 9, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2466_, 10, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2466_, 11, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2466_, 12, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2466_, 13, v_assignment_2435_);
lean_ctor_set(v_reuseFailAlloc_2466_, 14, v_nextCnstrId_2436_);
lean_ctor_set(v_reuseFailAlloc_2466_, 15, v_conflict_x3f_2438_);
lean_ctor_set(v_reuseFailAlloc_2466_, 16, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2466_, 17, v_divMod_2439_);
lean_ctor_set(v_reuseFailAlloc_2466_, 18, v_toIntIds_2440_);
lean_ctor_set(v_reuseFailAlloc_2466_, 19, v_toIntInfos_2441_);
lean_ctor_set(v_reuseFailAlloc_2466_, 20, v_toIntTermMap_2442_);
lean_ctor_set(v_reuseFailAlloc_2466_, 21, v_toIntVarMap_2443_);
lean_ctor_set(v_reuseFailAlloc_2466_, 22, v_nonlinearOccs_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, sizeof(void*)*23, v_caseSplits_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, sizeof(void*)*23 + 1, v_usedCommRing_2444_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object* v_a_2471_, lean_object* v___f_2472_, lean_object* v___x_2473_, lean_object* v_s_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(v_a_2471_, v___f_2472_, v___x_2473_, v_s_2474_);
lean_dec_ref(v___x_2473_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(lean_object* v_as_2476_, size_t v_i_2477_, size_t v_stop_2478_, lean_object* v_b_2479_){
_start:
{
lean_object* v___y_2481_; uint8_t v___x_2485_; 
v___x_2485_ = lean_usize_dec_eq(v_i_2477_, v_stop_2478_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_array_uget_borrowed(v_as_2476_, v_i_2477_);
if (lean_obj_tag(v___x_2486_) == 0)
{
v___y_2481_ = v_b_2479_;
goto v___jp_2480_;
}
else
{
lean_object* v_val_2487_; lean_object* v___x_2488_; 
v_val_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_val_2487_);
v___x_2488_ = lean_array_push(v_b_2479_, v_val_2487_);
v___y_2481_ = v___x_2488_;
goto v___jp_2480_;
}
}
else
{
return v_b_2479_;
}
v___jp_2480_:
{
size_t v___x_2482_; size_t v___x_2483_; 
v___x_2482_ = ((size_t)1ULL);
v___x_2483_ = lean_usize_add(v_i_2477_, v___x_2482_);
v_i_2477_ = v___x_2483_;
v_b_2479_ = v___y_2481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(lean_object* v_as_2489_, lean_object* v_i_2490_, lean_object* v_stop_2491_, lean_object* v_b_2492_){
_start:
{
size_t v_i_boxed_2493_; size_t v_stop_boxed_2494_; lean_object* v_res_2495_; 
v_i_boxed_2493_ = lean_unbox_usize(v_i_2490_);
lean_dec(v_i_2490_);
v_stop_boxed_2494_ = lean_unbox_usize(v_stop_2491_);
lean_dec(v_stop_2491_);
v_res_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_as_2489_, v_i_boxed_2493_, v_stop_boxed_2494_, v_b_2492_);
lean_dec_ref(v_as_2489_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(lean_object* v_x_2496_, lean_object* v_x_2497_){
_start:
{
if (lean_obj_tag(v_x_2496_) == 0)
{
lean_object* v_cs_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v_cs_2498_ = lean_ctor_get(v_x_2496_, 0);
v___x_2499_ = lean_unsigned_to_nat(0u);
v___x_2500_ = lean_array_get_size(v_cs_2498_);
v___x_2501_ = lean_nat_dec_lt(v___x_2499_, v___x_2500_);
if (v___x_2501_ == 0)
{
return v_x_2497_;
}
else
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_nat_dec_le(v___x_2500_, v___x_2500_);
if (v___x_2502_ == 0)
{
if (v___x_2501_ == 0)
{
return v_x_2497_;
}
else
{
size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = ((size_t)0ULL);
v___x_2504_ = lean_usize_of_nat(v___x_2500_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2498_, v___x_2503_, v___x_2504_, v_x_2497_);
return v___x_2505_;
}
}
else
{
size_t v___x_2506_; size_t v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = ((size_t)0ULL);
v___x_2507_ = lean_usize_of_nat(v___x_2500_);
v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2498_, v___x_2506_, v___x_2507_, v_x_2497_);
return v___x_2508_;
}
}
}
else
{
lean_object* v_vs_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_vs_2509_ = lean_ctor_get(v_x_2496_, 0);
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = lean_array_get_size(v_vs_2509_);
v___x_2512_ = lean_nat_dec_lt(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
return v_x_2497_;
}
else
{
uint8_t v___x_2513_; 
v___x_2513_ = lean_nat_dec_le(v___x_2511_, v___x_2511_);
if (v___x_2513_ == 0)
{
if (v___x_2512_ == 0)
{
return v_x_2497_;
}
else
{
size_t v___x_2514_; size_t v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = ((size_t)0ULL);
v___x_2515_ = lean_usize_of_nat(v___x_2511_);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2509_, v___x_2514_, v___x_2515_, v_x_2497_);
return v___x_2516_;
}
}
else
{
size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = ((size_t)0ULL);
v___x_2518_ = lean_usize_of_nat(v___x_2511_);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2509_, v___x_2517_, v___x_2518_, v_x_2497_);
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(lean_object* v_as_2520_, size_t v_i_2521_, size_t v_stop_2522_, lean_object* v_b_2523_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_usize_dec_eq(v_i_2521_, v_stop_2522_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; size_t v___x_2527_; size_t v___x_2528_; 
v___x_2525_ = lean_array_uget_borrowed(v_as_2520_, v_i_2521_);
v___x_2526_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v___x_2525_, v_b_2523_);
v___x_2527_ = ((size_t)1ULL);
v___x_2528_ = lean_usize_add(v_i_2521_, v___x_2527_);
v_i_2521_ = v___x_2528_;
v_b_2523_ = v___x_2526_;
goto _start;
}
else
{
return v_b_2523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25___boxed(lean_object* v_as_2530_, lean_object* v_i_2531_, lean_object* v_stop_2532_, lean_object* v_b_2533_){
_start:
{
size_t v_i_boxed_2534_; size_t v_stop_boxed_2535_; lean_object* v_res_2536_; 
v_i_boxed_2534_ = lean_unbox_usize(v_i_2531_);
lean_dec(v_i_2531_);
v_stop_boxed_2535_ = lean_unbox_usize(v_stop_2532_);
lean_dec(v_stop_2532_);
v_res_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_as_2530_, v_i_boxed_2534_, v_stop_boxed_2535_, v_b_2533_);
lean_dec_ref(v_as_2530_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20___boxed(lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_x_2537_, v_x_2538_);
lean_dec_ref(v_x_2537_);
return v_res_2539_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(lean_object* v_x_2541_, size_t v_x_2542_, size_t v_x_2543_, lean_object* v_x_2544_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
lean_object* v_cs_2545_; lean_object* v___x_2546_; size_t v___x_2547_; lean_object* v_j_2548_; lean_object* v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; size_t v___x_2552_; size_t v___x_2553_; size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v_cs_2545_ = lean_ctor_get(v_x_2541_, 0);
v___x_2546_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_2547_ = lean_usize_shift_right(v_x_2542_, v_x_2543_);
v_j_2548_ = lean_usize_to_nat(v___x_2547_);
v___x_2549_ = lean_array_get_borrowed(v___x_2546_, v_cs_2545_, v_j_2548_);
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_shift_left(v___x_2550_, v_x_2543_);
v___x_2552_ = lean_usize_sub(v___x_2551_, v___x_2550_);
v___x_2553_ = lean_usize_land(v_x_2542_, v___x_2552_);
v___x_2554_ = ((size_t)5ULL);
v___x_2555_ = lean_usize_sub(v_x_2543_, v___x_2554_);
v___x_2556_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v___x_2549_, v___x_2553_, v___x_2555_, v_x_2544_);
v___x_2557_ = lean_unsigned_to_nat(1u);
v___x_2558_ = lean_nat_add(v_j_2548_, v___x_2557_);
lean_dec(v_j_2548_);
v___x_2559_ = lean_array_get_size(v_cs_2545_);
v___x_2560_ = lean_nat_dec_lt(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_dec(v___x_2558_);
return v___x_2556_;
}
else
{
uint8_t v___x_2561_; 
v___x_2561_ = lean_nat_dec_le(v___x_2559_, v___x_2559_);
if (v___x_2561_ == 0)
{
if (v___x_2560_ == 0)
{
lean_dec(v___x_2558_);
return v___x_2556_;
}
else
{
size_t v___x_2562_; size_t v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = lean_usize_of_nat(v___x_2558_);
lean_dec(v___x_2558_);
v___x_2563_ = lean_usize_of_nat(v___x_2559_);
v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2545_, v___x_2562_, v___x_2563_, v___x_2556_);
return v___x_2564_;
}
}
else
{
size_t v___x_2565_; size_t v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = lean_usize_of_nat(v___x_2558_);
lean_dec(v___x_2558_);
v___x_2566_ = lean_usize_of_nat(v___x_2559_);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2545_, v___x_2565_, v___x_2566_, v___x_2556_);
return v___x_2567_;
}
}
}
else
{
lean_object* v_vs_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_vs_2568_ = lean_ctor_get(v_x_2541_, 0);
v___x_2569_ = lean_usize_to_nat(v_x_2542_);
v___x_2570_ = lean_array_get_size(v_vs_2568_);
v___x_2571_ = lean_nat_dec_lt(v___x_2569_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_dec(v___x_2569_);
return v_x_2544_;
}
else
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_nat_dec_le(v___x_2570_, v___x_2570_);
if (v___x_2572_ == 0)
{
if (v___x_2571_ == 0)
{
lean_dec(v___x_2569_);
return v_x_2544_;
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_usize_of_nat(v___x_2569_);
lean_dec(v___x_2569_);
v___x_2574_ = lean_usize_of_nat(v___x_2570_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2568_, v___x_2573_, v___x_2574_, v_x_2544_);
return v___x_2575_;
}
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_usize_of_nat(v___x_2569_);
lean_dec(v___x_2569_);
v___x_2577_ = lean_usize_of_nat(v___x_2570_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2568_, v___x_2576_, v___x_2577_, v_x_2544_);
return v___x_2578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___boxed(lean_object* v_x_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_){
_start:
{
size_t v_x_92062__boxed_2583_; size_t v_x_92063__boxed_2584_; lean_object* v_res_2585_; 
v_x_92062__boxed_2583_ = lean_unbox_usize(v_x_2580_);
lean_dec(v_x_2580_);
v_x_92063__boxed_2584_ = lean_unbox_usize(v_x_2581_);
lean_dec(v_x_2581_);
v_res_2585_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_x_2579_, v_x_92062__boxed_2583_, v_x_92063__boxed_2584_, v_x_2582_);
lean_dec_ref(v_x_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object* v_t_2586_, lean_object* v_init_2587_, lean_object* v_start_2588_){
_start:
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_nat_dec_eq(v_start_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v_root_2591_; lean_object* v_tail_2592_; size_t v_shift_2593_; lean_object* v_tailOff_2594_; uint8_t v___x_2595_; 
v_root_2591_ = lean_ctor_get(v_t_2586_, 0);
v_tail_2592_ = lean_ctor_get(v_t_2586_, 1);
v_shift_2593_ = lean_ctor_get_usize(v_t_2586_, 4);
v_tailOff_2594_ = lean_ctor_get(v_t_2586_, 3);
v___x_2595_ = lean_nat_dec_le(v_tailOff_2594_, v_start_2588_);
if (v___x_2595_ == 0)
{
size_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2596_ = lean_usize_of_nat(v_start_2588_);
v___x_2597_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_root_2591_, v___x_2596_, v_shift_2593_, v_init_2587_);
v___x_2598_ = lean_array_get_size(v_tail_2592_);
v___x_2599_ = lean_nat_dec_lt(v___x_2589_, v___x_2598_);
if (v___x_2599_ == 0)
{
return v___x_2597_;
}
else
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_nat_dec_le(v___x_2598_, v___x_2598_);
if (v___x_2600_ == 0)
{
if (v___x_2599_ == 0)
{
return v___x_2597_;
}
else
{
size_t v___x_2601_; size_t v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = ((size_t)0ULL);
v___x_2602_ = lean_usize_of_nat(v___x_2598_);
v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2592_, v___x_2601_, v___x_2602_, v___x_2597_);
return v___x_2603_;
}
}
else
{
size_t v___x_2604_; size_t v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = ((size_t)0ULL);
v___x_2605_ = lean_usize_of_nat(v___x_2598_);
v___x_2606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2592_, v___x_2604_, v___x_2605_, v___x_2597_);
return v___x_2606_;
}
}
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2607_ = lean_nat_sub(v_start_2588_, v_tailOff_2594_);
v___x_2608_ = lean_array_get_size(v_tail_2592_);
v___x_2609_ = lean_nat_dec_lt(v___x_2607_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_dec(v___x_2607_);
return v_init_2587_;
}
else
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_nat_dec_le(v___x_2608_, v___x_2608_);
if (v___x_2610_ == 0)
{
if (v___x_2609_ == 0)
{
lean_dec(v___x_2607_);
return v_init_2587_;
}
else
{
size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_usize_of_nat(v___x_2607_);
lean_dec(v___x_2607_);
v___x_2612_ = lean_usize_of_nat(v___x_2608_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2592_, v___x_2611_, v___x_2612_, v_init_2587_);
return v___x_2613_;
}
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_usize_of_nat(v___x_2607_);
lean_dec(v___x_2607_);
v___x_2615_ = lean_usize_of_nat(v___x_2608_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2592_, v___x_2614_, v___x_2615_, v_init_2587_);
return v___x_2616_;
}
}
}
}
else
{
lean_object* v_root_2617_; lean_object* v_tail_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_root_2617_ = lean_ctor_get(v_t_2586_, 0);
v_tail_2618_ = lean_ctor_get(v_t_2586_, 1);
v___x_2619_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_root_2617_, v_init_2587_);
v___x_2620_ = lean_array_get_size(v_tail_2618_);
v___x_2621_ = lean_nat_dec_lt(v___x_2589_, v___x_2620_);
if (v___x_2621_ == 0)
{
return v___x_2619_;
}
else
{
uint8_t v___x_2622_; 
v___x_2622_ = lean_nat_dec_le(v___x_2620_, v___x_2620_);
if (v___x_2622_ == 0)
{
if (v___x_2621_ == 0)
{
return v___x_2619_;
}
else
{
size_t v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = ((size_t)0ULL);
v___x_2624_ = lean_usize_of_nat(v___x_2620_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2618_, v___x_2623_, v___x_2624_, v___x_2619_);
return v___x_2625_;
}
}
else
{
size_t v___x_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = ((size_t)0ULL);
v___x_2627_ = lean_usize_of_nat(v___x_2620_);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2618_, v___x_2626_, v___x_2627_, v___x_2619_);
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___boxed(lean_object* v_t_2629_, lean_object* v_init_2630_, lean_object* v_start_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_t_2629_, v_init_2630_, v_start_2631_);
lean_dec(v_start_2631_);
lean_dec_ref(v_t_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(lean_object* v_as_2633_, size_t v_i_2634_, size_t v_stop_2635_, lean_object* v_b_2636_){
_start:
{
uint8_t v___x_2637_; 
v___x_2637_ = lean_usize_dec_eq(v_i_2634_, v_stop_2635_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; size_t v___x_2641_; size_t v___x_2642_; 
v___x_2638_ = lean_array_uget_borrowed(v_as_2633_, v_i_2634_);
v___x_2639_ = l_Lean_PersistentArray_toArray___redArg(v___x_2638_);
v___x_2640_ = l_Array_append___redArg(v_b_2636_, v___x_2639_);
lean_dec_ref(v___x_2639_);
v___x_2641_ = ((size_t)1ULL);
v___x_2642_ = lean_usize_add(v_i_2634_, v___x_2641_);
v_i_2634_ = v___x_2642_;
v_b_2636_ = v___x_2640_;
goto _start;
}
else
{
return v_b_2636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23___boxed(lean_object* v_as_2644_, lean_object* v_i_2645_, lean_object* v_stop_2646_, lean_object* v_b_2647_){
_start:
{
size_t v_i_boxed_2648_; size_t v_stop_boxed_2649_; lean_object* v_res_2650_; 
v_i_boxed_2648_ = lean_unbox_usize(v_i_2645_);
lean_dec(v_i_2645_);
v_stop_boxed_2649_ = lean_unbox_usize(v_stop_2646_);
lean_dec(v_stop_2646_);
v_res_2650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_as_2644_, v_i_boxed_2648_, v_stop_boxed_2649_, v_b_2647_);
lean_dec_ref(v_as_2644_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(lean_object* v_x_2651_, lean_object* v_x_2652_){
_start:
{
if (lean_obj_tag(v_x_2651_) == 0)
{
lean_object* v_cs_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v_cs_2653_ = lean_ctor_get(v_x_2651_, 0);
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_array_get_size(v_cs_2653_);
v___x_2656_ = lean_nat_dec_lt(v___x_2654_, v___x_2655_);
if (v___x_2656_ == 0)
{
return v_x_2652_;
}
else
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_nat_dec_le(v___x_2655_, v___x_2655_);
if (v___x_2657_ == 0)
{
if (v___x_2656_ == 0)
{
return v_x_2652_;
}
else
{
size_t v___x_2658_; size_t v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = lean_usize_of_nat(v___x_2655_);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2653_, v___x_2658_, v___x_2659_, v_x_2652_);
return v___x_2660_;
}
}
else
{
size_t v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = lean_usize_of_nat(v___x_2655_);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2653_, v___x_2661_, v___x_2662_, v_x_2652_);
return v___x_2663_;
}
}
}
else
{
lean_object* v_vs_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v_vs_2664_ = lean_ctor_get(v_x_2651_, 0);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get_size(v_vs_2664_);
v___x_2667_ = lean_nat_dec_lt(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
return v_x_2652_;
}
else
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_nat_dec_le(v___x_2666_, v___x_2666_);
if (v___x_2668_ == 0)
{
if (v___x_2667_ == 0)
{
return v_x_2652_;
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2666_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2664_, v___x_2669_, v___x_2670_, v_x_2652_);
return v___x_2671_;
}
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2666_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2664_, v___x_2672_, v___x_2673_, v_x_2652_);
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(lean_object* v_as_2675_, size_t v_i_2676_, size_t v_stop_2677_, lean_object* v_b_2678_){
_start:
{
uint8_t v___x_2679_; 
v___x_2679_ = lean_usize_dec_eq(v_i_2676_, v_stop_2677_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; size_t v___x_2682_; size_t v___x_2683_; 
v___x_2680_ = lean_array_uget_borrowed(v_as_2675_, v_i_2676_);
v___x_2681_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v___x_2680_, v_b_2678_);
v___x_2682_ = ((size_t)1ULL);
v___x_2683_ = lean_usize_add(v_i_2676_, v___x_2682_);
v_i_2676_ = v___x_2683_;
v_b_2678_ = v___x_2681_;
goto _start;
}
else
{
return v_b_2678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30___boxed(lean_object* v_as_2685_, lean_object* v_i_2686_, lean_object* v_stop_2687_, lean_object* v_b_2688_){
_start:
{
size_t v_i_boxed_2689_; size_t v_stop_boxed_2690_; lean_object* v_res_2691_; 
v_i_boxed_2689_ = lean_unbox_usize(v_i_2686_);
lean_dec(v_i_2686_);
v_stop_boxed_2690_ = lean_unbox_usize(v_stop_2687_);
lean_dec(v_stop_2687_);
v_res_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_as_2685_, v_i_boxed_2689_, v_stop_boxed_2690_, v_b_2688_);
lean_dec_ref(v_as_2685_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(lean_object* v_x_2692_, lean_object* v_x_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_x_2692_, v_x_2693_);
lean_dec_ref(v_x_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(lean_object* v_x_2695_, size_t v_x_2696_, size_t v_x_2697_, lean_object* v_x_2698_){
_start:
{
if (lean_obj_tag(v_x_2695_) == 0)
{
lean_object* v_cs_2699_; lean_object* v___x_2700_; size_t v___x_2701_; lean_object* v_j_2702_; lean_object* v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v_cs_2699_ = lean_ctor_get(v_x_2695_, 0);
v___x_2700_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_2701_ = lean_usize_shift_right(v_x_2696_, v_x_2697_);
v_j_2702_ = lean_usize_to_nat(v___x_2701_);
v___x_2703_ = lean_array_get_borrowed(v___x_2700_, v_cs_2699_, v_j_2702_);
v___x_2704_ = ((size_t)1ULL);
v___x_2705_ = lean_usize_shift_left(v___x_2704_, v_x_2697_);
v___x_2706_ = lean_usize_sub(v___x_2705_, v___x_2704_);
v___x_2707_ = lean_usize_land(v_x_2696_, v___x_2706_);
v___x_2708_ = ((size_t)5ULL);
v___x_2709_ = lean_usize_sub(v_x_2697_, v___x_2708_);
v___x_2710_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v___x_2703_, v___x_2707_, v___x_2709_, v_x_2698_);
v___x_2711_ = lean_unsigned_to_nat(1u);
v___x_2712_ = lean_nat_add(v_j_2702_, v___x_2711_);
lean_dec(v_j_2702_);
v___x_2713_ = lean_array_get_size(v_cs_2699_);
v___x_2714_ = lean_nat_dec_lt(v___x_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_dec(v___x_2712_);
return v___x_2710_;
}
else
{
uint8_t v___x_2715_; 
v___x_2715_ = lean_nat_dec_le(v___x_2713_, v___x_2713_);
if (v___x_2715_ == 0)
{
if (v___x_2714_ == 0)
{
lean_dec(v___x_2712_);
return v___x_2710_;
}
else
{
size_t v___x_2716_; size_t v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = lean_usize_of_nat(v___x_2712_);
lean_dec(v___x_2712_);
v___x_2717_ = lean_usize_of_nat(v___x_2713_);
v___x_2718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2699_, v___x_2716_, v___x_2717_, v___x_2710_);
return v___x_2718_;
}
}
else
{
size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_usize_of_nat(v___x_2712_);
lean_dec(v___x_2712_);
v___x_2720_ = lean_usize_of_nat(v___x_2713_);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2699_, v___x_2719_, v___x_2720_, v___x_2710_);
return v___x_2721_;
}
}
}
else
{
lean_object* v_vs_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_vs_2722_ = lean_ctor_get(v_x_2695_, 0);
v___x_2723_ = lean_usize_to_nat(v_x_2696_);
v___x_2724_ = lean_array_get_size(v_vs_2722_);
v___x_2725_ = lean_nat_dec_lt(v___x_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_dec(v___x_2723_);
return v_x_2698_;
}
else
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_nat_dec_le(v___x_2724_, v___x_2724_);
if (v___x_2726_ == 0)
{
if (v___x_2725_ == 0)
{
lean_dec(v___x_2723_);
return v_x_2698_;
}
else
{
size_t v___x_2727_; size_t v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_usize_of_nat(v___x_2723_);
lean_dec(v___x_2723_);
v___x_2728_ = lean_usize_of_nat(v___x_2724_);
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2722_, v___x_2727_, v___x_2728_, v_x_2698_);
return v___x_2729_;
}
}
else
{
size_t v___x_2730_; size_t v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_usize_of_nat(v___x_2723_);
lean_dec(v___x_2723_);
v___x_2731_ = lean_usize_of_nat(v___x_2724_);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2722_, v___x_2730_, v___x_2731_, v_x_2698_);
return v___x_2732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(lean_object* v_x_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_, lean_object* v_x_2736_){
_start:
{
size_t v_x_92286__boxed_2737_; size_t v_x_92287__boxed_2738_; lean_object* v_res_2739_; 
v_x_92286__boxed_2737_ = lean_unbox_usize(v_x_2734_);
lean_dec(v_x_2734_);
v_x_92287__boxed_2738_ = lean_unbox_usize(v_x_2735_);
lean_dec(v_x_2735_);
v_res_2739_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_x_2733_, v_x_92286__boxed_2737_, v_x_92287__boxed_2738_, v_x_2736_);
lean_dec_ref(v_x_2733_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object* v_t_2740_, lean_object* v_init_2741_, lean_object* v_start_2742_){
_start:
{
lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = lean_nat_dec_eq(v_start_2742_, v___x_2743_);
if (v___x_2744_ == 0)
{
lean_object* v_root_2745_; lean_object* v_tail_2746_; size_t v_shift_2747_; lean_object* v_tailOff_2748_; uint8_t v___x_2749_; 
v_root_2745_ = lean_ctor_get(v_t_2740_, 0);
v_tail_2746_ = lean_ctor_get(v_t_2740_, 1);
v_shift_2747_ = lean_ctor_get_usize(v_t_2740_, 4);
v_tailOff_2748_ = lean_ctor_get(v_t_2740_, 3);
v___x_2749_ = lean_nat_dec_le(v_tailOff_2748_, v_start_2742_);
if (v___x_2749_ == 0)
{
size_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2750_ = lean_usize_of_nat(v_start_2742_);
v___x_2751_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_root_2745_, v___x_2750_, v_shift_2747_, v_init_2741_);
v___x_2752_ = lean_array_get_size(v_tail_2746_);
v___x_2753_ = lean_nat_dec_lt(v___x_2743_, v___x_2752_);
if (v___x_2753_ == 0)
{
return v___x_2751_;
}
else
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_nat_dec_le(v___x_2752_, v___x_2752_);
if (v___x_2754_ == 0)
{
if (v___x_2753_ == 0)
{
return v___x_2751_;
}
else
{
size_t v___x_2755_; size_t v___x_2756_; lean_object* v___x_2757_; 
v___x_2755_ = ((size_t)0ULL);
v___x_2756_ = lean_usize_of_nat(v___x_2752_);
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2746_, v___x_2755_, v___x_2756_, v___x_2751_);
return v___x_2757_;
}
}
else
{
size_t v___x_2758_; size_t v___x_2759_; lean_object* v___x_2760_; 
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = lean_usize_of_nat(v___x_2752_);
v___x_2760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2746_, v___x_2758_, v___x_2759_, v___x_2751_);
return v___x_2760_;
}
}
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2761_ = lean_nat_sub(v_start_2742_, v_tailOff_2748_);
v___x_2762_ = lean_array_get_size(v_tail_2746_);
v___x_2763_ = lean_nat_dec_lt(v___x_2761_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_dec(v___x_2761_);
return v_init_2741_;
}
else
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_nat_dec_le(v___x_2762_, v___x_2762_);
if (v___x_2764_ == 0)
{
if (v___x_2763_ == 0)
{
lean_dec(v___x_2761_);
return v_init_2741_;
}
else
{
size_t v___x_2765_; size_t v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = lean_usize_of_nat(v___x_2761_);
lean_dec(v___x_2761_);
v___x_2766_ = lean_usize_of_nat(v___x_2762_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2746_, v___x_2765_, v___x_2766_, v_init_2741_);
return v___x_2767_;
}
}
else
{
size_t v___x_2768_; size_t v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = lean_usize_of_nat(v___x_2761_);
lean_dec(v___x_2761_);
v___x_2769_ = lean_usize_of_nat(v___x_2762_);
v___x_2770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2746_, v___x_2768_, v___x_2769_, v_init_2741_);
return v___x_2770_;
}
}
}
}
else
{
lean_object* v_root_2771_; lean_object* v_tail_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v_root_2771_ = lean_ctor_get(v_t_2740_, 0);
v_tail_2772_ = lean_ctor_get(v_t_2740_, 1);
v___x_2773_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_root_2771_, v_init_2741_);
v___x_2774_ = lean_array_get_size(v_tail_2772_);
v___x_2775_ = lean_nat_dec_lt(v___x_2743_, v___x_2774_);
if (v___x_2775_ == 0)
{
return v___x_2773_;
}
else
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_nat_dec_le(v___x_2774_, v___x_2774_);
if (v___x_2776_ == 0)
{
if (v___x_2775_ == 0)
{
return v___x_2773_;
}
else
{
size_t v___x_2777_; size_t v___x_2778_; lean_object* v___x_2779_; 
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = lean_usize_of_nat(v___x_2774_);
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2772_, v___x_2777_, v___x_2778_, v___x_2773_);
return v___x_2779_;
}
}
else
{
size_t v___x_2780_; size_t v___x_2781_; lean_object* v___x_2782_; 
v___x_2780_ = ((size_t)0ULL);
v___x_2781_ = lean_usize_of_nat(v___x_2774_);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2772_, v___x_2780_, v___x_2781_, v___x_2773_);
return v___x_2782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object* v_t_2783_, lean_object* v_init_2784_, lean_object* v_start_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_t_2783_, v_init_2784_, v_start_2785_);
lean_dec(v_start_2785_);
lean_dec_ref(v_t_2783_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object* v___x_2787_, size_t v_sz_2788_, size_t v_i_2789_, lean_object* v_bs_2790_){
_start:
{
uint8_t v___x_2791_; 
v___x_2791_ = lean_usize_dec_lt(v_i_2789_, v_sz_2788_);
if (v___x_2791_ == 0)
{
return v_bs_2790_;
}
else
{
lean_object* v_v_2792_; lean_object* v___x_2793_; lean_object* v_bs_x27_2794_; lean_object* v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; lean_object* v___x_2798_; 
v_v_2792_ = lean_array_uget(v_bs_2790_, v_i_2789_);
v___x_2793_ = lean_unsigned_to_nat(0u);
v_bs_x27_2794_ = lean_array_uset(v_bs_2790_, v_i_2789_, v___x_2793_);
v___x_2795_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_v_2792_, v___x_2787_);
v___x_2796_ = ((size_t)1ULL);
v___x_2797_ = lean_usize_add(v_i_2789_, v___x_2796_);
v___x_2798_ = lean_array_uset(v_bs_x27_2794_, v_i_2789_, v___x_2795_);
v_i_2789_ = v___x_2797_;
v_bs_2790_ = v___x_2798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object* v___x_2800_, lean_object* v_sz_2801_, lean_object* v_i_2802_, lean_object* v_bs_2803_){
_start:
{
size_t v_sz_boxed_2804_; size_t v_i_boxed_2805_; lean_object* v_res_2806_; 
v_sz_boxed_2804_ = lean_unbox_usize(v_sz_2801_);
lean_dec(v_sz_2801_);
v_i_boxed_2805_ = lean_unbox_usize(v_i_2802_);
lean_dec(v_i_2802_);
v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_2800_, v_sz_boxed_2804_, v_i_boxed_2805_, v_bs_2803_);
lean_dec_ref(v___x_2800_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object* v___x_2807_, size_t v_sz_2808_, size_t v_i_2809_, lean_object* v_bs_2810_){
_start:
{
uint8_t v___x_2811_; 
v___x_2811_ = lean_usize_dec_lt(v_i_2809_, v_sz_2808_);
if (v___x_2811_ == 0)
{
return v_bs_2810_;
}
else
{
lean_object* v_v_2812_; lean_object* v___x_2813_; lean_object* v_bs_x27_2814_; lean_object* v___x_2815_; size_t v___x_2816_; size_t v___x_2817_; lean_object* v___x_2818_; 
v_v_2812_ = lean_array_uget(v_bs_2810_, v_i_2809_);
v___x_2813_ = lean_unsigned_to_nat(0u);
v_bs_x27_2814_ = lean_array_uset(v_bs_2810_, v_i_2809_, v___x_2813_);
v___x_2815_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_v_2812_, v___x_2807_);
v___x_2816_ = ((size_t)1ULL);
v___x_2817_ = lean_usize_add(v_i_2809_, v___x_2816_);
v___x_2818_ = lean_array_uset(v_bs_x27_2814_, v_i_2809_, v___x_2815_);
v_i_2809_ = v___x_2817_;
v_bs_2810_ = v___x_2818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object* v___x_2820_, lean_object* v_sz_2821_, lean_object* v_i_2822_, lean_object* v_bs_2823_){
_start:
{
size_t v_sz_boxed_2824_; size_t v_i_boxed_2825_; lean_object* v_res_2826_; 
v_sz_boxed_2824_ = lean_unbox_usize(v_sz_2821_);
lean_dec(v_sz_2821_);
v_i_boxed_2825_ = lean_unbox_usize(v_i_2822_);
lean_dec(v_i_2822_);
v_res_2826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_2820_, v_sz_boxed_2824_, v_i_boxed_2825_, v_bs_2823_);
lean_dec_ref(v___x_2820_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(lean_object* v_msgData_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; lean_object* v_env_2834_; lean_object* v___x_2835_; lean_object* v_mctx_2836_; lean_object* v_lctx_2837_; lean_object* v_options_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2833_ = lean_st_ref_get(v___y_2831_);
v_env_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc_ref(v_env_2834_);
lean_dec(v___x_2833_);
v___x_2835_ = lean_st_ref_get(v___y_2829_);
v_mctx_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc_ref(v_mctx_2836_);
lean_dec(v___x_2835_);
v_lctx_2837_ = lean_ctor_get(v___y_2828_, 2);
v_options_2838_ = lean_ctor_get(v___y_2830_, 2);
lean_inc_ref(v_options_2838_);
lean_inc_ref(v_lctx_2837_);
v___x_2839_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2839_, 0, v_env_2834_);
lean_ctor_set(v___x_2839_, 1, v_mctx_2836_);
lean_ctor_set(v___x_2839_, 2, v_lctx_2837_);
lean_ctor_set(v___x_2839_, 3, v_options_2838_);
v___x_2840_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v_msgData_2827_);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37___boxed(lean_object* v_msgData_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(v_msgData_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
return v_res_2848_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_2849_; double v___x_2850_; 
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_float_of_nat(v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(lean_object* v_cls_2854_, lean_object* v_msg_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_ref_2861_; lean_object* v___x_2862_; lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2907_; 
v_ref_2861_ = lean_ctor_get(v___y_2858_, 5);
v___x_2862_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(v_msg_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2907_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2907_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v_traceState_2868_; lean_object* v_env_2869_; lean_object* v_nextMacroScope_2870_; lean_object* v_ngen_2871_; lean_object* v_auxDeclNGen_2872_; lean_object* v_cache_2873_; lean_object* v_messages_2874_; lean_object* v_infoState_2875_; lean_object* v_snapshotTasks_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2906_; 
v___x_2867_ = lean_st_ref_take(v___y_2859_);
v_traceState_2868_ = lean_ctor_get(v___x_2867_, 4);
v_env_2869_ = lean_ctor_get(v___x_2867_, 0);
v_nextMacroScope_2870_ = lean_ctor_get(v___x_2867_, 1);
v_ngen_2871_ = lean_ctor_get(v___x_2867_, 2);
v_auxDeclNGen_2872_ = lean_ctor_get(v___x_2867_, 3);
v_cache_2873_ = lean_ctor_get(v___x_2867_, 5);
v_messages_2874_ = lean_ctor_get(v___x_2867_, 6);
v_infoState_2875_ = lean_ctor_get(v___x_2867_, 7);
v_snapshotTasks_2876_ = lean_ctor_get(v___x_2867_, 8);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2878_ = v___x_2867_;
v_isShared_2879_ = v_isSharedCheck_2906_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_snapshotTasks_2876_);
lean_inc(v_infoState_2875_);
lean_inc(v_messages_2874_);
lean_inc(v_cache_2873_);
lean_inc(v_traceState_2868_);
lean_inc(v_auxDeclNGen_2872_);
lean_inc(v_ngen_2871_);
lean_inc(v_nextMacroScope_2870_);
lean_inc(v_env_2869_);
lean_dec(v___x_2867_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2906_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint64_t v_tid_2880_; lean_object* v_traces_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2905_; 
v_tid_2880_ = lean_ctor_get_uint64(v_traceState_2868_, sizeof(void*)*1);
v_traces_2881_ = lean_ctor_get(v_traceState_2868_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_traceState_2868_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2883_ = v_traceState_2868_;
v_isShared_2884_ = v_isSharedCheck_2905_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_traces_2881_);
lean_dec(v_traceState_2868_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2905_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; double v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0);
v___x_2887_ = 0;
v___x_2888_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1));
v___x_2889_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2889_, 0, v_cls_2854_);
lean_ctor_set(v___x_2889_, 1, v___x_2885_);
lean_ctor_set(v___x_2889_, 2, v___x_2888_);
lean_ctor_set_float(v___x_2889_, sizeof(void*)*3, v___x_2886_);
lean_ctor_set_float(v___x_2889_, sizeof(void*)*3 + 8, v___x_2886_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*3 + 16, v___x_2887_);
v___x_2890_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2));
v___x_2891_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v_a_2863_);
lean_ctor_set(v___x_2891_, 2, v___x_2890_);
lean_inc(v_ref_2861_);
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v_ref_2861_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = l_Lean_PersistentArray_push___redArg(v_traces_2881_, v___x_2892_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2893_);
v___x_2895_ = v___x_2883_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2893_);
lean_ctor_set_uint64(v_reuseFailAlloc_2904_, sizeof(void*)*1, v_tid_2880_);
v___x_2895_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2897_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 4, v___x_2895_);
v___x_2897_ = v___x_2878_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_env_2869_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_nextMacroScope_2870_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_ngen_2871_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_auxDeclNGen_2872_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_cache_2873_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_messages_2874_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_infoState_2875_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_snapshotTasks_2876_);
v___x_2897_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2898_ = lean_st_ref_set(v___y_2859_, v___x_2897_);
v___x_2899_ = lean_box(0);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2899_);
v___x_2901_ = v___x_2865_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___boxed(lean_object* v_cls_2908_, lean_object* v_msg_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v_cls_2908_, v_msg_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object* v___x_2916_, size_t v_sz_2917_, size_t v_i_2918_, lean_object* v_bs_2919_){
_start:
{
uint8_t v___x_2920_; 
v___x_2920_ = lean_usize_dec_lt(v_i_2918_, v_sz_2917_);
if (v___x_2920_ == 0)
{
return v_bs_2919_;
}
else
{
lean_object* v_v_2921_; lean_object* v___x_2922_; lean_object* v_bs_x27_2923_; lean_object* v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; 
v_v_2921_ = lean_array_uget(v_bs_2919_, v_i_2918_);
v___x_2922_ = lean_unsigned_to_nat(0u);
v_bs_x27_2923_ = lean_array_uset(v_bs_2919_, v_i_2918_, v___x_2922_);
v___x_2924_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_2921_, v___x_2916_);
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_add(v_i_2918_, v___x_2925_);
v___x_2927_ = lean_array_uset(v_bs_x27_2923_, v_i_2918_, v___x_2924_);
v_i_2918_ = v___x_2926_;
v_bs_2919_ = v___x_2927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object* v___x_2929_, lean_object* v_sz_2930_, lean_object* v_i_2931_, lean_object* v_bs_2932_){
_start:
{
size_t v_sz_boxed_2933_; size_t v_i_boxed_2934_; lean_object* v_res_2935_; 
v_sz_boxed_2933_ = lean_unbox_usize(v_sz_2930_);
lean_dec(v_sz_2930_);
v_i_boxed_2934_ = lean_unbox_usize(v_i_2931_);
lean_dec(v_i_2931_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_2929_, v_sz_boxed_2933_, v_i_boxed_2934_, v_bs_2932_);
lean_dec_ref(v___x_2929_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object* v_as_2936_, size_t v_sz_2937_, size_t v_i_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_lt(v_i_2938_, v_sz_2937_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_b_2939_);
return v___x_2952_;
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2954_; 
v_a_2953_ = lean_array_uget_borrowed(v_as_2936_, v_i_2938_);
lean_inc(v_a_2953_);
v___x_2954_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(v_a_2953_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; 
lean_dec_ref(v___x_2954_);
v___x_2955_ = lean_box(0);
v___x_2956_ = ((size_t)1ULL);
v___x_2957_ = lean_usize_add(v_i_2938_, v___x_2956_);
v_i_2938_ = v___x_2957_;
v_b_2939_ = v___x_2955_;
goto _start;
}
else
{
return v___x_2954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object* v_as_2959_, lean_object* v_sz_2960_, lean_object* v_i_2961_, lean_object* v_b_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
size_t v_sz_boxed_2974_; size_t v_i_boxed_2975_; lean_object* v_res_2976_; 
v_sz_boxed_2974_ = lean_unbox_usize(v_sz_2960_);
lean_dec(v_sz_2960_);
v_i_boxed_2975_ = lean_unbox_usize(v_i_2961_);
lean_dec(v_i_2961_);
v_res_2976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_2959_, v_sz_boxed_2974_, v_i_boxed_2975_, v_b_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v_as_2959_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object* v_as_2977_, size_t v_sz_2978_, size_t v_i_2979_, lean_object* v_b_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_usize_dec_lt(v_i_2979_, v_sz_2978_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v_b_2980_);
return v___x_2993_;
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_array_uget_borrowed(v_as_2977_, v_i_2979_);
lean_inc(v___y_2990_);
lean_inc_ref(v___y_2989_);
lean_inc(v___y_2988_);
lean_inc_ref(v___y_2987_);
lean_inc(v___y_2986_);
lean_inc_ref(v___y_2985_);
lean_inc(v___y_2984_);
lean_inc_ref(v___y_2983_);
lean_inc(v___y_2982_);
lean_inc(v___y_2981_);
lean_inc(v_a_2994_);
v___x_2995_ = lean_grind_cutsat_assert_le(v_a_2994_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v___x_2996_; size_t v___x_2997_; size_t v___x_2998_; 
lean_dec_ref(v___x_2995_);
v___x_2996_ = lean_box(0);
v___x_2997_ = ((size_t)1ULL);
v___x_2998_ = lean_usize_add(v_i_2979_, v___x_2997_);
v_i_2979_ = v___x_2998_;
v_b_2980_ = v___x_2996_;
goto _start;
}
else
{
return v___x_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object* v_as_3000_, lean_object* v_sz_3001_, lean_object* v_i_3002_, lean_object* v_b_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
size_t v_sz_boxed_3015_; size_t v_i_boxed_3016_; lean_object* v_res_3017_; 
v_sz_boxed_3015_ = lean_unbox_usize(v_sz_3001_);
lean_dec(v_sz_3001_);
v_i_boxed_3016_ = lean_unbox_usize(v_i_3002_);
lean_dec(v_i_3002_);
v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v_as_3000_, v_sz_boxed_3015_, v_i_boxed_3016_, v_b_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v_as_3000_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
if (lean_obj_tag(v_a_3018_) == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = l_List_reverse___redArg(v_a_3019_);
return v___x_3020_;
}
else
{
lean_object* v_head_3021_; lean_object* v_tail_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3033_; 
v_head_3021_ = lean_ctor_get(v_a_3018_, 0);
v_tail_3022_ = lean_ctor_get(v_a_3018_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_a_3018_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3024_ = v_a_3018_;
v_isShared_3025_ = v_isSharedCheck_3033_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_tail_3022_);
lean_inc(v_head_3021_);
lean_dec(v_a_3018_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3033_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3026_ = l_Nat_reprFast(v_head_3021_);
v___x_3027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
v___x_3028_ = l_Lean_MessageData_ofFormat(v___x_3027_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 1, v_a_3019_);
lean_ctor_set(v___x_3024_, 0, v___x_3028_);
v___x_3030_ = v___x_3024_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_a_3019_);
v___x_3030_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
v_a_3018_ = v_tail_3022_;
v_a_3019_ = v___x_3030_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object* v_as_3034_, size_t v_sz_3035_, size_t v_i_3036_, lean_object* v_b_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_usize_dec_lt(v_i_3036_, v_sz_3035_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_b_3037_);
return v___x_3050_;
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3052_; 
v_a_3051_ = lean_array_uget_borrowed(v_as_3034_, v_i_3036_);
lean_inc_ref(v___y_3046_);
lean_inc(v_a_3051_);
v___x_3052_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_a_3051_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3053_; size_t v___x_3054_; size_t v___x_3055_; 
lean_dec_ref(v___x_3052_);
v___x_3053_ = lean_box(0);
v___x_3054_ = ((size_t)1ULL);
v___x_3055_ = lean_usize_add(v_i_3036_, v___x_3054_);
v_i_3036_ = v___x_3055_;
v_b_3037_ = v___x_3053_;
goto _start;
}
else
{
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object* v_as_3057_, lean_object* v_sz_3058_, lean_object* v_i_3059_, lean_object* v_b_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
size_t v_sz_boxed_3072_; size_t v_i_boxed_3073_; lean_object* v_res_3074_; 
v_sz_boxed_3072_ = lean_unbox_usize(v_sz_3058_);
lean_dec(v_sz_3058_);
v_i_boxed_3073_ = lean_unbox_usize(v_i_3059_);
lean_dec(v_i_3059_);
v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v_as_3057_, v_sz_boxed_3072_, v_i_boxed_3073_, v_b_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v_as_3057_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(lean_object* v_as_3075_, size_t v_i_3076_, size_t v_stop_3077_, lean_object* v_b_3078_){
_start:
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_usize_dec_eq(v_i_3076_, v_stop_3077_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; size_t v___x_3083_; size_t v___x_3084_; 
v___x_3080_ = lean_array_uget_borrowed(v_as_3075_, v_i_3076_);
v___x_3081_ = l_Lean_PersistentArray_toArray___redArg(v___x_3080_);
v___x_3082_ = l_Array_append___redArg(v_b_3078_, v___x_3081_);
lean_dec_ref(v___x_3081_);
v___x_3083_ = ((size_t)1ULL);
v___x_3084_ = lean_usize_add(v_i_3076_, v___x_3083_);
v_i_3076_ = v___x_3084_;
v_b_3078_ = v___x_3082_;
goto _start;
}
else
{
return v_b_3078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(lean_object* v_as_3086_, lean_object* v_i_3087_, lean_object* v_stop_3088_, lean_object* v_b_3089_){
_start:
{
size_t v_i_boxed_3090_; size_t v_stop_boxed_3091_; lean_object* v_res_3092_; 
v_i_boxed_3090_ = lean_unbox_usize(v_i_3087_);
lean_dec(v_i_3087_);
v_stop_boxed_3091_ = lean_unbox_usize(v_stop_3088_);
lean_dec(v_stop_3088_);
v_res_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_as_3086_, v_i_boxed_3090_, v_stop_boxed_3091_, v_b_3089_);
lean_dec_ref(v_as_3086_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(lean_object* v_x_3093_, lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3093_) == 0)
{
lean_object* v_cs_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_cs_3095_ = lean_ctor_get(v_x_3093_, 0);
v___x_3096_ = lean_unsigned_to_nat(0u);
v___x_3097_ = lean_array_get_size(v_cs_3095_);
v___x_3098_ = lean_nat_dec_lt(v___x_3096_, v___x_3097_);
if (v___x_3098_ == 0)
{
return v_x_3094_;
}
else
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_nat_dec_le(v___x_3097_, v___x_3097_);
if (v___x_3099_ == 0)
{
if (v___x_3098_ == 0)
{
return v_x_3094_;
}
else
{
size_t v___x_3100_; size_t v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = lean_usize_of_nat(v___x_3097_);
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3095_, v___x_3100_, v___x_3101_, v_x_3094_);
return v___x_3102_;
}
}
else
{
size_t v___x_3103_; size_t v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = ((size_t)0ULL);
v___x_3104_ = lean_usize_of_nat(v___x_3097_);
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3095_, v___x_3103_, v___x_3104_, v_x_3094_);
return v___x_3105_;
}
}
}
else
{
lean_object* v_vs_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v_vs_3106_ = lean_ctor_get(v_x_3093_, 0);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = lean_array_get_size(v_vs_3106_);
v___x_3109_ = lean_nat_dec_lt(v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
return v_x_3094_;
}
else
{
uint8_t v___x_3110_; 
v___x_3110_ = lean_nat_dec_le(v___x_3108_, v___x_3108_);
if (v___x_3110_ == 0)
{
if (v___x_3109_ == 0)
{
return v_x_3094_;
}
else
{
size_t v___x_3111_; size_t v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = ((size_t)0ULL);
v___x_3112_ = lean_usize_of_nat(v___x_3108_);
v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3106_, v___x_3111_, v___x_3112_, v_x_3094_);
return v___x_3113_;
}
}
else
{
size_t v___x_3114_; size_t v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = ((size_t)0ULL);
v___x_3115_ = lean_usize_of_nat(v___x_3108_);
v___x_3116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3106_, v___x_3114_, v___x_3115_, v_x_3094_);
return v___x_3116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(lean_object* v_as_3117_, size_t v_i_3118_, size_t v_stop_3119_, lean_object* v_b_3120_){
_start:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_usize_dec_eq(v_i_3118_, v_stop_3119_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; size_t v___x_3124_; size_t v___x_3125_; 
v___x_3122_ = lean_array_uget_borrowed(v_as_3117_, v_i_3118_);
v___x_3123_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v___x_3122_, v_b_3120_);
v___x_3124_ = ((size_t)1ULL);
v___x_3125_ = lean_usize_add(v_i_3118_, v___x_3124_);
v_i_3118_ = v___x_3125_;
v_b_3120_ = v___x_3123_;
goto _start;
}
else
{
return v_b_3120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35___boxed(lean_object* v_as_3127_, lean_object* v_i_3128_, lean_object* v_stop_3129_, lean_object* v_b_3130_){
_start:
{
size_t v_i_boxed_3131_; size_t v_stop_boxed_3132_; lean_object* v_res_3133_; 
v_i_boxed_3131_ = lean_unbox_usize(v_i_3128_);
lean_dec(v_i_3128_);
v_stop_boxed_3132_ = lean_unbox_usize(v_stop_3129_);
lean_dec(v_stop_3129_);
v_res_3133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_as_3127_, v_i_boxed_3131_, v_stop_boxed_3132_, v_b_3130_);
lean_dec_ref(v_as_3127_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28___boxed(lean_object* v_x_3134_, lean_object* v_x_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_x_3134_, v_x_3135_);
lean_dec_ref(v_x_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(lean_object* v_x_3137_, size_t v_x_3138_, size_t v_x_3139_, lean_object* v_x_3140_){
_start:
{
if (lean_obj_tag(v_x_3137_) == 0)
{
lean_object* v_cs_3141_; lean_object* v___x_3142_; size_t v___x_3143_; lean_object* v_j_3144_; lean_object* v___x_3145_; size_t v___x_3146_; size_t v___x_3147_; size_t v___x_3148_; size_t v___x_3149_; size_t v___x_3150_; size_t v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v_cs_3141_ = lean_ctor_get(v_x_3137_, 0);
v___x_3142_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_3143_ = lean_usize_shift_right(v_x_3138_, v_x_3139_);
v_j_3144_ = lean_usize_to_nat(v___x_3143_);
v___x_3145_ = lean_array_get_borrowed(v___x_3142_, v_cs_3141_, v_j_3144_);
v___x_3146_ = ((size_t)1ULL);
v___x_3147_ = lean_usize_shift_left(v___x_3146_, v_x_3139_);
v___x_3148_ = lean_usize_sub(v___x_3147_, v___x_3146_);
v___x_3149_ = lean_usize_land(v_x_3138_, v___x_3148_);
v___x_3150_ = ((size_t)5ULL);
v___x_3151_ = lean_usize_sub(v_x_3139_, v___x_3150_);
v___x_3152_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v___x_3145_, v___x_3149_, v___x_3151_, v_x_3140_);
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_nat_add(v_j_3144_, v___x_3153_);
lean_dec(v_j_3144_);
v___x_3155_ = lean_array_get_size(v_cs_3141_);
v___x_3156_ = lean_nat_dec_lt(v___x_3154_, v___x_3155_);
if (v___x_3156_ == 0)
{
lean_dec(v___x_3154_);
return v___x_3152_;
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_nat_dec_le(v___x_3155_, v___x_3155_);
if (v___x_3157_ == 0)
{
if (v___x_3156_ == 0)
{
lean_dec(v___x_3154_);
return v___x_3152_;
}
else
{
size_t v___x_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = lean_usize_of_nat(v___x_3154_);
lean_dec(v___x_3154_);
v___x_3159_ = lean_usize_of_nat(v___x_3155_);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3141_, v___x_3158_, v___x_3159_, v___x_3152_);
return v___x_3160_;
}
}
else
{
size_t v___x_3161_; size_t v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_usize_of_nat(v___x_3154_);
lean_dec(v___x_3154_);
v___x_3162_ = lean_usize_of_nat(v___x_3155_);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3141_, v___x_3161_, v___x_3162_, v___x_3152_);
return v___x_3163_;
}
}
}
else
{
lean_object* v_vs_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v_vs_3164_ = lean_ctor_get(v_x_3137_, 0);
v___x_3165_ = lean_usize_to_nat(v_x_3138_);
v___x_3166_ = lean_array_get_size(v_vs_3164_);
v___x_3167_ = lean_nat_dec_lt(v___x_3165_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_dec(v___x_3165_);
return v_x_3140_;
}
else
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_nat_dec_le(v___x_3166_, v___x_3166_);
if (v___x_3168_ == 0)
{
if (v___x_3167_ == 0)
{
lean_dec(v___x_3165_);
return v_x_3140_;
}
else
{
size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_usize_of_nat(v___x_3165_);
lean_dec(v___x_3165_);
v___x_3170_ = lean_usize_of_nat(v___x_3166_);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3164_, v___x_3169_, v___x_3170_, v_x_3140_);
return v___x_3171_;
}
}
else
{
size_t v___x_3172_; size_t v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_usize_of_nat(v___x_3165_);
lean_dec(v___x_3165_);
v___x_3173_ = lean_usize_of_nat(v___x_3166_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3164_, v___x_3172_, v___x_3173_, v_x_3140_);
return v___x_3174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26___boxed(lean_object* v_x_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_, lean_object* v_x_3178_){
_start:
{
size_t v_x_92865__boxed_3179_; size_t v_x_92866__boxed_3180_; lean_object* v_res_3181_; 
v_x_92865__boxed_3179_ = lean_unbox_usize(v_x_3176_);
lean_dec(v_x_3176_);
v_x_92866__boxed_3180_ = lean_unbox_usize(v_x_3177_);
lean_dec(v_x_3177_);
v_res_3181_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_x_3175_, v_x_92865__boxed_3179_, v_x_92866__boxed_3180_, v_x_3178_);
lean_dec_ref(v_x_3175_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object* v_t_3182_, lean_object* v_init_3183_, lean_object* v_start_3184_){
_start:
{
lean_object* v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = lean_unsigned_to_nat(0u);
v___x_3186_ = lean_nat_dec_eq(v_start_3184_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v_root_3187_; lean_object* v_tail_3188_; size_t v_shift_3189_; lean_object* v_tailOff_3190_; uint8_t v___x_3191_; 
v_root_3187_ = lean_ctor_get(v_t_3182_, 0);
v_tail_3188_ = lean_ctor_get(v_t_3182_, 1);
v_shift_3189_ = lean_ctor_get_usize(v_t_3182_, 4);
v_tailOff_3190_ = lean_ctor_get(v_t_3182_, 3);
v___x_3191_ = lean_nat_dec_le(v_tailOff_3190_, v_start_3184_);
if (v___x_3191_ == 0)
{
size_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v___x_3192_ = lean_usize_of_nat(v_start_3184_);
v___x_3193_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_root_3187_, v___x_3192_, v_shift_3189_, v_init_3183_);
v___x_3194_ = lean_array_get_size(v_tail_3188_);
v___x_3195_ = lean_nat_dec_lt(v___x_3185_, v___x_3194_);
if (v___x_3195_ == 0)
{
return v___x_3193_;
}
else
{
uint8_t v___x_3196_; 
v___x_3196_ = lean_nat_dec_le(v___x_3194_, v___x_3194_);
if (v___x_3196_ == 0)
{
if (v___x_3195_ == 0)
{
return v___x_3193_;
}
else
{
size_t v___x_3197_; size_t v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = ((size_t)0ULL);
v___x_3198_ = lean_usize_of_nat(v___x_3194_);
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3188_, v___x_3197_, v___x_3198_, v___x_3193_);
return v___x_3199_;
}
}
else
{
size_t v___x_3200_; size_t v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = ((size_t)0ULL);
v___x_3201_ = lean_usize_of_nat(v___x_3194_);
v___x_3202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3188_, v___x_3200_, v___x_3201_, v___x_3193_);
return v___x_3202_;
}
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v___x_3203_ = lean_nat_sub(v_start_3184_, v_tailOff_3190_);
v___x_3204_ = lean_array_get_size(v_tail_3188_);
v___x_3205_ = lean_nat_dec_lt(v___x_3203_, v___x_3204_);
if (v___x_3205_ == 0)
{
lean_dec(v___x_3203_);
return v_init_3183_;
}
else
{
uint8_t v___x_3206_; 
v___x_3206_ = lean_nat_dec_le(v___x_3204_, v___x_3204_);
if (v___x_3206_ == 0)
{
if (v___x_3205_ == 0)
{
lean_dec(v___x_3203_);
return v_init_3183_;
}
else
{
size_t v___x_3207_; size_t v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_usize_of_nat(v___x_3203_);
lean_dec(v___x_3203_);
v___x_3208_ = lean_usize_of_nat(v___x_3204_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3188_, v___x_3207_, v___x_3208_, v_init_3183_);
return v___x_3209_;
}
}
else
{
size_t v___x_3210_; size_t v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_usize_of_nat(v___x_3203_);
lean_dec(v___x_3203_);
v___x_3211_ = lean_usize_of_nat(v___x_3204_);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3188_, v___x_3210_, v___x_3211_, v_init_3183_);
return v___x_3212_;
}
}
}
}
else
{
lean_object* v_root_3213_; lean_object* v_tail_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v_root_3213_ = lean_ctor_get(v_t_3182_, 0);
v_tail_3214_ = lean_ctor_get(v_t_3182_, 1);
v___x_3215_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_root_3213_, v_init_3183_);
v___x_3216_ = lean_array_get_size(v_tail_3214_);
v___x_3217_ = lean_nat_dec_lt(v___x_3185_, v___x_3216_);
if (v___x_3217_ == 0)
{
return v___x_3215_;
}
else
{
uint8_t v___x_3218_; 
v___x_3218_ = lean_nat_dec_le(v___x_3216_, v___x_3216_);
if (v___x_3218_ == 0)
{
if (v___x_3217_ == 0)
{
return v___x_3215_;
}
else
{
size_t v___x_3219_; size_t v___x_3220_; lean_object* v___x_3221_; 
v___x_3219_ = ((size_t)0ULL);
v___x_3220_ = lean_usize_of_nat(v___x_3216_);
v___x_3221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3214_, v___x_3219_, v___x_3220_, v___x_3215_);
return v___x_3221_;
}
}
else
{
size_t v___x_3222_; size_t v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = ((size_t)0ULL);
v___x_3223_ = lean_usize_of_nat(v___x_3216_);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3214_, v___x_3222_, v___x_3223_, v___x_3215_);
return v___x_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object* v_t_3225_, lean_object* v_init_3226_, lean_object* v_start_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_t_3225_, v_init_3226_, v_start_3227_);
lean_dec(v_start_3227_);
lean_dec_ref(v_t_3225_);
return v_res_3228_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6));
v___x_3246_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8));
v___x_3247_ = l_Lean_Name_append(v___x_3246_, v___x_3245_);
return v___x_3247_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3250_ = l_Lean_stringToMessageData(v___x_3249_);
return v___x_3250_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12));
v___x_3253_ = l_Lean_stringToMessageData(v___x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3254_, v_a_3262_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3360_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3360_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3360_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v_vars_3270_; lean_object* v_vars_x27_3271_; lean_object* v_dvds_3272_; lean_object* v_lowers_3273_; lean_object* v_uppers_3274_; lean_object* v_diseqs_3275_; uint8_t v___x_3276_; 
v_vars_3270_ = lean_ctor_get(v_a_3266_, 0);
lean_inc_ref(v_vars_3270_);
v_vars_x27_3271_ = lean_ctor_get(v_a_3266_, 2);
lean_inc_ref(v_vars_x27_3271_);
v_dvds_3272_ = lean_ctor_get(v_a_3266_, 6);
lean_inc_ref(v_dvds_3272_);
v_lowers_3273_ = lean_ctor_get(v_a_3266_, 7);
lean_inc_ref(v_lowers_3273_);
v_uppers_3274_ = lean_ctor_get(v_a_3266_, 8);
lean_inc_ref(v_uppers_3274_);
v_diseqs_3275_ = lean_ctor_get(v_a_3266_, 9);
lean_inc_ref(v_diseqs_3275_);
lean_dec(v_a_3266_);
v___x_3276_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_3270_);
lean_dec_ref(v_vars_3270_);
if (v___x_3276_ == 0)
{
uint8_t v___x_3277_; 
v___x_3277_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_x27_3271_);
lean_dec_ref(v_vars_x27_3271_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3280_; 
lean_dec_ref(v_diseqs_3275_);
lean_dec_ref(v_uppers_3274_);
lean_dec_ref(v_lowers_3273_);
lean_dec_ref(v_dvds_3272_);
v___x_3278_ = lean_box(0);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3278_);
v___x_3280_ = v___x_3268_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
else
{
lean_object* v___x_3282_; 
lean_del_object(v___x_3268_);
v___x_3282_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v___x_3283_; 
lean_dec_ref(v___x_3282_);
v___x_3283_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3285_; lean_object* v___f_3286_; lean_object* v___f_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc_n(v_a_3284_, 2);
lean_dec_ref(v___x_3283_);
v___x_3285_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_3284_);
lean_inc_ref_n(v___x_3285_, 2);
v___f_3286_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3286_, 0, v___x_3285_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3287_, 0, v_a_3284_);
lean_closure_set(v___f_3287_, 1, v___f_3286_);
lean_closure_set(v___f_3287_, 2, v___x_3285_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0));
v___x_3290_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_dvds_3272_, v___x_3289_, v___x_3288_);
lean_dec_ref(v_dvds_3272_);
v___x_3291_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_lowers_3273_, v___x_3289_, v___x_3288_);
lean_dec_ref(v_lowers_3273_);
v___x_3292_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3293_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3292_, v___f_3287_, v_a_3254_);
if (lean_obj_tag(v___x_3293_) == 0)
{
size_t v_sz_3294_; size_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; size_t v_sz_3298_; lean_object* v___x_3299_; 
lean_dec_ref(v___x_3293_);
v_sz_3294_ = lean_array_size(v___x_3290_);
v___x_3295_ = ((size_t)0ULL);
v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_3285_, v_sz_3294_, v___x_3295_, v___x_3290_);
v___x_3297_ = lean_box(0);
v_sz_3298_ = lean_array_size(v___x_3296_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_3296_, v_sz_3298_, v___x_3295_, v___x_3297_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec_ref(v___x_3296_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v___x_3300_; size_t v_sz_3301_; lean_object* v___x_3302_; size_t v_sz_3303_; lean_object* v___x_3304_; 
lean_dec_ref(v___x_3299_);
v___x_3300_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_uppers_3274_, v___x_3291_, v___x_3288_);
lean_dec_ref(v_uppers_3274_);
v_sz_3301_ = lean_array_size(v___x_3300_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_3285_, v_sz_3301_, v___x_3295_, v___x_3300_);
v_sz_3303_ = lean_array_size(v___x_3302_);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_3302_, v_sz_3303_, v___x_3295_, v___x_3297_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec_ref(v___x_3302_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v___x_3305_; size_t v_sz_3306_; lean_object* v___x_3307_; size_t v_sz_3308_; lean_object* v___x_3309_; 
lean_dec_ref(v___x_3304_);
v___x_3305_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_diseqs_3275_, v___x_3289_, v___x_3288_);
lean_dec_ref(v_diseqs_3275_);
v_sz_3306_ = lean_array_size(v___x_3305_);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_3285_, v_sz_3306_, v___x_3295_, v___x_3305_);
v_sz_3308_ = lean_array_size(v___x_3307_);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_3307_, v_sz_3308_, v___x_3295_, v___x_3297_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec_ref(v___x_3307_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_options_3310_; uint8_t v_hasTrace_3311_; 
lean_dec_ref(v___x_3309_);
v_options_3310_ = lean_ctor_get(v_a_3262_, 2);
v_hasTrace_3311_ = lean_ctor_get_uint8(v_options_3310_, sizeof(void*)*1);
if (v_hasTrace_3311_ == 0)
{
lean_object* v___x_3312_; 
lean_dec_ref(v___x_3285_);
lean_dec(v_a_3284_);
v___x_3312_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
return v___x_3312_;
}
else
{
lean_object* v_inheritedTraceOptions_3313_; lean_object* v___x_3314_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v_options_3325_; lean_object* v_inheritedTraceOptions_3326_; lean_object* v___y_3327_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v_inheritedTraceOptions_3313_ = lean_ctor_get(v_a_3262_, 13);
v___x_3314_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6));
v___x_3339_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9);
v___x_3340_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3313_, v_options_3310_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_dec(v_a_3284_);
v___y_3316_ = v_a_3254_;
v___y_3317_ = v_a_3255_;
v___y_3318_ = v_a_3256_;
v___y_3319_ = v_a_3257_;
v___y_3320_ = v_a_3258_;
v___y_3321_ = v_a_3259_;
v___y_3322_ = v_a_3260_;
v___y_3323_ = v_a_3261_;
v___y_3324_ = v_a_3262_;
v_options_3325_ = v_options_3310_;
v_inheritedTraceOptions_3326_ = v_inheritedTraceOptions_3313_;
v___y_3327_ = v_a_3263_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3341_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13);
v___x_3342_ = lean_array_to_list(v_a_3284_);
v___x_3343_ = lean_box(0);
v___x_3344_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3342_, v___x_3343_);
v___x_3345_ = l_Lean_MessageData_ofList(v___x_3344_);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3341_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v___x_3314_, v___x_3346_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_dec_ref(v___x_3347_);
v___y_3316_ = v_a_3254_;
v___y_3317_ = v_a_3255_;
v___y_3318_ = v_a_3256_;
v___y_3319_ = v_a_3257_;
v___y_3320_ = v_a_3258_;
v___y_3321_ = v_a_3259_;
v___y_3322_ = v_a_3260_;
v___y_3323_ = v_a_3261_;
v___y_3324_ = v_a_3262_;
v_options_3325_ = v_options_3310_;
v_inheritedTraceOptions_3326_ = v_inheritedTraceOptions_3313_;
v___y_3327_ = v_a_3263_;
goto v___jp_3315_;
}
else
{
lean_dec_ref(v___x_3285_);
return v___x_3347_;
}
}
v___jp_3315_:
{
lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3328_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9);
v___x_3329_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3326_, v_options_3325_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_dec_ref(v___x_3285_);
v___x_3330_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3327_);
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3331_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11);
v___x_3332_ = lean_array_to_list(v___x_3285_);
v___x_3333_ = lean_box(0);
v___x_3334_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3332_, v___x_3333_);
v___x_3335_ = l_Lean_MessageData_ofList(v___x_3334_);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3331_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v___x_3314_, v___x_3336_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3327_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v___x_3338_; 
lean_dec_ref(v___x_3337_);
v___x_3338_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3327_);
return v___x_3338_;
}
else
{
return v___x_3337_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3285_);
lean_dec(v_a_3284_);
return v___x_3309_;
}
}
else
{
lean_dec_ref(v___x_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_diseqs_3275_);
return v___x_3304_;
}
}
else
{
lean_dec_ref(v___x_3291_);
lean_dec_ref(v___x_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_diseqs_3275_);
lean_dec_ref(v_uppers_3274_);
return v___x_3299_;
}
}
else
{
lean_dec_ref(v___x_3291_);
lean_dec_ref(v___x_3290_);
lean_dec_ref(v___x_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_diseqs_3275_);
lean_dec_ref(v_uppers_3274_);
return v___x_3293_;
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v_diseqs_3275_);
lean_dec_ref(v_uppers_3274_);
lean_dec_ref(v_lowers_3273_);
lean_dec_ref(v_dvds_3272_);
v_a_3348_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3283_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3283_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_dec_ref(v_diseqs_3275_);
lean_dec_ref(v_uppers_3274_);
lean_dec_ref(v_lowers_3273_);
lean_dec_ref(v_dvds_3272_);
return v___x_3282_;
}
}
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
lean_dec_ref(v_diseqs_3275_);
lean_dec_ref(v_uppers_3274_);
lean_dec_ref(v_lowers_3273_);
lean_dec_ref(v_dvds_3272_);
lean_dec_ref(v_vars_x27_3271_);
v___x_3356_ = lean_box(0);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3356_);
v___x_3358_ = v___x_3268_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
v_a_3361_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3265_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3265_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_a_3370_);
lean_dec(v_a_3369_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object* v_00_u03b2_3381_, lean_object* v_00_u03c3_3382_, lean_object* v_pm_3383_, lean_object* v_f_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_pm_3383_, v_f_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object* v_cls_3386_, lean_object* v_msg_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v_cls_3386_, v_msg_3387_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___boxed(lean_object* v_cls_3400_, lean_object* v_msg_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v_cls_3400_, v_msg_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec(v___y_3402_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(lean_object* v_pm_3414_, lean_object* v_f_3415_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3415_, v_pm_3414_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(lean_object* v_00_u03b2_3417_, lean_object* v_00_u03c3_3418_, lean_object* v_pm_3419_, lean_object* v_f_3420_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3420_, v_pm_3419_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3422_, lean_object* v_00_u03b2_3423_, lean_object* v_00_u03c3_3424_, lean_object* v_f_3425_, lean_object* v_n_3426_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3425_, v_n_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(lean_object* v_00_u03b1_3428_, lean_object* v_00_u03b2_3429_, lean_object* v_00_u03c3_3430_, lean_object* v_f_3431_, size_t v_sz_3432_, size_t v_i_3433_, lean_object* v_bs_3434_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_3431_, v_sz_3432_, v_i_3433_, v_bs_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___boxed(lean_object* v_00_u03b1_3436_, lean_object* v_00_u03b2_3437_, lean_object* v_00_u03c3_3438_, lean_object* v_f_3439_, lean_object* v_sz_3440_, lean_object* v_i_3441_, lean_object* v_bs_3442_){
_start:
{
size_t v_sz_boxed_3443_; size_t v_i_boxed_3444_; lean_object* v_res_3445_; 
v_sz_boxed_3443_ = lean_unbox_usize(v_sz_3440_);
lean_dec(v_sz_3440_);
v_i_boxed_3444_ = lean_unbox_usize(v_i_3441_);
lean_dec(v_i_3441_);
v_res_3445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(v_00_u03b1_3436_, v_00_u03b2_3437_, v_00_u03c3_3438_, v_f_3439_, v_sz_boxed_3443_, v_i_boxed_3444_, v_bs_3442_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(lean_object* v_00_u03b1_3446_, lean_object* v_00_u03b2_3447_, lean_object* v_f_3448_, lean_object* v_as_3449_){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_3448_, v_as_3449_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___boxed(lean_object* v_00_u03b1_3451_, lean_object* v_00_u03b2_3452_, lean_object* v_f_3453_, lean_object* v_as_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(v_00_u03b1_3451_, v_00_u03b2_3452_, v_f_3453_, v_as_3454_);
lean_dec_ref(v_as_3454_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(lean_object* v_00_u03b1_3456_, lean_object* v_00_u03b2_3457_, lean_object* v_f_3458_, lean_object* v_as_3459_, lean_object* v_i_3460_, lean_object* v_acc_3461_, lean_object* v_hle_3462_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_3458_, v_as_3459_, v_i_3460_, v_acc_3461_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___boxed(lean_object* v_00_u03b1_3464_, lean_object* v_00_u03b2_3465_, lean_object* v_f_3466_, lean_object* v_as_3467_, lean_object* v_i_3468_, lean_object* v_acc_3469_, lean_object* v_hle_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(v_00_u03b1_3464_, v_00_u03b2_3465_, v_f_3466_, v_as_3467_, v_i_3468_, v_acc_3469_, v_hle_3470_);
lean_dec_ref(v_as_3467_);
return v_res_3471_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
}
#ifdef __cplusplus
}
#endif
