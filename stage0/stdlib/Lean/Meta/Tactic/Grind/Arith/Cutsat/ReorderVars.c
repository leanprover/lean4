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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__22(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "old2new: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "new2old: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object* v_inh_479_, lean_object* v_n_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
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
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_inh_479_, v_cs_494_, v_sz_500_, v___x_501_, v___x_499_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object* v_inh_604_, lean_object* v_as_605_, size_t v_sz_606_, size_t v_i_607_, lean_object* v_b_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
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
v___x_629_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_inh_604_, v_a_628_, v_snd_624_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
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
lean_object* v_inh_676_ = _args[0];
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
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_inh_676_, v_as_677_, v_sz_boxed_693_, v_i_boxed_694_, v_b_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object* v_inh_696_, lean_object* v_n_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_inh_696_, v_n_697_, v_b_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
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
lean_dec_ref(v_a_814_);
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
lean_inc_ref(v_lowers_853_);
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
lean_inc_ref(v_dvds_852_);
v___x_865_ = l_Lean_PersistentArray_get_x21___redArg(v___x_862_, v_dvds_852_, v_i_817_);
v___y_843_ = v_snd_860_;
v___y_844_ = v___x_865_;
goto v___jp_842_;
}
}
else
{
lean_dec(v_i_817_);
lean_dec_ref(v_a_814_);
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
lean_inc_ref(v_uppers_854_);
v___x_874_ = l_Lean_PersistentArray_get_x21___redArg(v___x_866_, v_uppers_854_, v_i_817_);
v___y_856_ = v_snd_871_;
v___y_857_ = v___x_874_;
goto v___jp_855_;
}
}
else
{
lean_dec(v_i_817_);
lean_dec_ref(v_a_814_);
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
lean_dec_ref(v_a_814_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg(lean_object* v_cls_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_options_1886_; uint8_t v_hasTrace_1887_; 
v_options_1886_ = lean_ctor_get(v___y_1884_, 2);
v_hasTrace_1887_ = lean_ctor_get_uint8(v_options_1886_, sizeof(void*)*1);
if (v_hasTrace_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec(v_cls_1883_);
v___x_1888_ = lean_box(v_hasTrace_1887_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
else
{
lean_object* v_inheritedTraceOptions_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_inheritedTraceOptions_1890_ = lean_ctor_get(v___y_1884_, 13);
v___x_1891_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___closed__1));
v___x_1892_ = l_Lean_Name_append(v___x_1891_, v_cls_1883_);
v___x_1893_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1890_, v_options_1886_, v___x_1892_);
lean_dec(v___x_1892_);
v___x_1894_ = lean_box(v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg___boxed(lean_object* v_cls_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg(v_cls_1896_, v___y_1897_);
lean_dec_ref(v___y_1897_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object* v_cls_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg(v_cls_1900_, v___y_1909_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object* v_cls_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v_cls_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec(v___y_1914_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object* v___x_1926_, lean_object* v_x_1927_){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_unsigned_to_nat(0u);
v___x_1929_ = lean_array_get_borrowed(v___x_1928_, v___x_1926_, v_x_1927_);
lean_inc(v___x_1929_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object* v___x_1930_, lean_object* v_x_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_1930_, v_x_1931_);
lean_dec(v_x_1931_);
lean_dec_ref(v___x_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___redArg(lean_object* v_f_1933_, lean_object* v_as_1934_, lean_object* v_i_1935_, lean_object* v_acc_1936_){
_start:
{
lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = lean_array_get_size(v_as_1934_);
v___x_1938_ = lean_nat_dec_eq(v_i_1935_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1939_ = lean_array_fget_borrowed(v_as_1934_, v_i_1935_);
lean_inc(v_f_1933_);
lean_inc(v___x_1939_);
v___x_1940_ = lean_apply_1(v_f_1933_, v___x_1939_);
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = lean_nat_add(v_i_1935_, v___x_1941_);
lean_dec(v_i_1935_);
v___x_1943_ = lean_array_push(v_acc_1936_, v___x_1940_);
v_i_1935_ = v___x_1942_;
v_acc_1936_ = v___x_1943_;
goto _start;
}
else
{
lean_dec(v_i_1935_);
lean_dec(v_f_1933_);
return v_acc_1936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___redArg___boxed(lean_object* v_f_1945_, lean_object* v_as_1946_, lean_object* v_i_1947_, lean_object* v_acc_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___redArg(v_f_1945_, v_as_1946_, v_i_1947_, v_acc_1948_);
lean_dec_ref(v_as_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___redArg(lean_object* v_f_1950_, lean_object* v_as_1951_){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_array_get_size(v_as_1951_);
v___x_1954_ = lean_mk_empty_array_with_capacity(v___x_1953_);
v___x_1955_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___redArg(v_f_1950_, v_as_1951_, v___x_1952_, v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___redArg___boxed(lean_object* v_f_1956_, lean_object* v_as_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___redArg(v_f_1956_, v_as_1957_);
lean_dec_ref(v_as_1957_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___redArg(lean_object* v_f_1959_, size_t v_sz_1960_, size_t v_i_1961_, lean_object* v_bs_1962_){
_start:
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_usize_dec_lt(v_i_1961_, v_sz_1960_);
if (v___x_1963_ == 0)
{
lean_dec(v_f_1959_);
return v_bs_1962_;
}
else
{
lean_object* v_v_1964_; lean_object* v___x_1965_; lean_object* v_bs_x27_1966_; lean_object* v___y_1968_; 
v_v_1964_ = lean_array_uget(v_bs_1962_, v_i_1961_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v_bs_x27_1966_ = lean_array_uset(v_bs_1962_, v_i_1961_, v___x_1965_);
switch(lean_obj_tag(v_v_1964_))
{
case 0:
{
lean_object* v_key_1973_; lean_object* v_val_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1982_; 
v_key_1973_ = lean_ctor_get(v_v_1964_, 0);
v_val_1974_ = lean_ctor_get(v_v_1964_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_v_1964_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1976_ = v_v_1964_;
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_val_1974_);
lean_inc(v_key_1973_);
lean_dec(v_v_1964_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_inc(v_f_1959_);
v___x_1978_ = lean_apply_1(v_f_1959_, v_val_1974_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v___x_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_key_1973_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
v___y_1968_ = v___x_1980_;
goto v___jp_1967_;
}
}
}
case 1:
{
lean_object* v_node_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1991_; 
v_node_1983_ = lean_ctor_get(v_v_1964_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_v_1964_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1985_ = v_v_1964_;
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_node_1983_);
lean_dec(v_v_1964_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
lean_inc(v_f_1959_);
v___x_1987_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2___redArg(v_f_1959_, v_node_1983_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1987_);
v___x_1989_ = v___x_1985_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
v___y_1968_ = v___x_1989_;
goto v___jp_1967_;
}
}
}
default: 
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_box(2);
v___y_1968_ = v___x_1992_;
goto v___jp_1967_;
}
}
v___jp_1967_:
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1961_, v___x_1969_);
v___x_1971_ = lean_array_uset(v_bs_x27_1966_, v_i_1961_, v___y_1968_);
v_i_1961_ = v___x_1970_;
v_bs_1962_ = v___x_1971_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2___redArg(lean_object* v_f_1993_, lean_object* v_n_1994_){
_start:
{
if (lean_obj_tag(v_n_1994_) == 0)
{
lean_object* v_es_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_es_1995_ = lean_ctor_get(v_n_1994_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_n_1994_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1997_ = v_n_1994_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_es_1995_);
lean_dec(v_n_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
size_t v_sz_1999_; size_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v_sz_1999_ = lean_array_size(v_es_1995_);
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___redArg(v_f_1993_, v_sz_1999_, v___x_2000_, v_es_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2001_);
v___x_2003_ = v___x_1997_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
else
{
lean_object* v_ks_2006_; lean_object* v_vs_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2015_; 
v_ks_2006_ = lean_ctor_get(v_n_1994_, 0);
v_vs_2007_ = lean_ctor_get(v_n_1994_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_n_1994_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2009_ = v_n_1994_;
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_vs_2007_);
lean_inc(v_ks_2006_);
lean_dec(v_n_1994_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_val_2011_; lean_object* v___x_2013_; 
v_val_2011_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___redArg(v_f_1993_, v_vs_2007_);
lean_dec_ref(v_vs_2007_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v_val_2011_);
v___x_2013_ = v___x_2009_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_ks_2006_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_val_2011_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___redArg___boxed(lean_object* v_f_2016_, lean_object* v_sz_2017_, lean_object* v_i_2018_, lean_object* v_bs_2019_){
_start:
{
size_t v_sz_boxed_2020_; size_t v_i_boxed_2021_; lean_object* v_res_2022_; 
v_sz_boxed_2020_ = lean_unbox_usize(v_sz_2017_);
lean_dec(v_sz_2017_);
v_i_boxed_2021_ = lean_unbox_usize(v_i_2018_);
lean_dec(v_i_2018_);
v_res_2022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___redArg(v_f_2016_, v_sz_boxed_2020_, v_i_boxed_2021_, v_bs_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(lean_object* v_f_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_apply_1(v_f_2023_, v_x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(lean_object* v_pm_2026_, lean_object* v_f_2027_){
_start:
{
lean_object* v___f_2028_; lean_object* v___x_2029_; 
v___f_2028_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2028_, 0, v_f_2027_);
v___x_2029_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2___redArg(v___f_2028_, v_pm_2026_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(lean_object* v___x_2030_, size_t v_sz_2031_, size_t v_i_2032_, lean_object* v_bs_2033_){
_start:
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_usize_dec_lt(v_i_2032_, v_sz_2031_);
if (v___x_2034_ == 0)
{
return v_bs_2033_;
}
else
{
lean_object* v_v_2035_; lean_object* v___x_2036_; lean_object* v_bs_x27_2037_; lean_object* v___y_2039_; 
v_v_2035_ = lean_array_uget(v_bs_2033_, v_i_2032_);
v___x_2036_ = lean_unsigned_to_nat(0u);
v_bs_x27_2037_ = lean_array_uset(v_bs_2033_, v_i_2032_, v___x_2036_);
if (lean_obj_tag(v_v_2035_) == 0)
{
v___y_2039_ = v_v_2035_;
goto v___jp_2038_;
}
else
{
lean_object* v_val_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2052_; 
v_val_2044_ = lean_ctor_get(v_v_2035_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_v_2035_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2046_ = v_v_2035_;
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_val_2044_);
lean_dec(v_v_2035_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_2044_, v___x_2030_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2048_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
v___y_2039_ = v___x_2050_;
goto v___jp_2038_;
}
}
}
v___jp_2038_:
{
size_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = ((size_t)1ULL);
v___x_2041_ = lean_usize_add(v_i_2032_, v___x_2040_);
v___x_2042_ = lean_array_uset(v_bs_x27_2037_, v_i_2032_, v___y_2039_);
v_i_2032_ = v___x_2041_;
v_bs_2033_ = v___x_2042_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(lean_object* v___x_2053_, lean_object* v_sz_2054_, lean_object* v_i_2055_, lean_object* v_bs_2056_){
_start:
{
size_t v_sz_boxed_2057_; size_t v_i_boxed_2058_; lean_object* v_res_2059_; 
v_sz_boxed_2057_ = lean_unbox_usize(v_sz_2054_);
lean_dec(v_sz_2054_);
v_i_boxed_2058_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2053_, v_sz_boxed_2057_, v_i_boxed_2058_, v_bs_2056_);
lean_dec_ref(v___x_2053_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__17(lean_object* v___x_2060_, size_t v_sz_2061_, size_t v_i_2062_, lean_object* v_bs_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = lean_usize_dec_lt(v_i_2062_, v_sz_2061_);
if (v___x_2064_ == 0)
{
return v_bs_2063_;
}
else
{
lean_object* v_v_2065_; lean_object* v___x_2066_; lean_object* v_bs_x27_2067_; lean_object* v___x_2068_; size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v_v_2065_ = lean_array_uget(v_bs_2063_, v_i_2062_);
v___x_2066_ = lean_unsigned_to_nat(0u);
v_bs_x27_2067_ = lean_array_uset(v_bs_2063_, v_i_2062_, v___x_2066_);
v___x_2068_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2060_, v_v_2065_);
v___x_2069_ = ((size_t)1ULL);
v___x_2070_ = lean_usize_add(v_i_2062_, v___x_2069_);
v___x_2071_ = lean_array_uset(v_bs_x27_2067_, v_i_2062_, v___x_2068_);
v_i_2062_ = v___x_2070_;
v_bs_2063_ = v___x_2071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(lean_object* v___x_2073_, lean_object* v_x_2074_){
_start:
{
if (lean_obj_tag(v_x_2074_) == 0)
{
lean_object* v_cs_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2085_; 
v_cs_2075_ = lean_ctor_get(v_x_2074_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_x_2074_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2077_ = v_x_2074_;
v_isShared_2078_ = v_isSharedCheck_2085_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_cs_2075_);
lean_dec(v_x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2085_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
size_t v_sz_2079_; size_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v_sz_2079_ = lean_array_size(v_cs_2075_);
v___x_2080_ = ((size_t)0ULL);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__17(v___x_2073_, v_sz_2079_, v___x_2080_, v_cs_2075_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2081_);
v___x_2083_ = v___x_2077_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_object* v_vs_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2096_; 
v_vs_2086_ = lean_ctor_get(v_x_2074_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_x_2074_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2088_ = v_x_2074_;
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_vs_2086_);
lean_dec(v_x_2074_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
size_t v_sz_2090_; size_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v_sz_2090_ = lean_array_size(v_vs_2086_);
v___x_2091_ = ((size_t)0ULL);
v___x_2092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2073_, v_sz_2090_, v___x_2091_, v_vs_2086_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2092_);
v___x_2094_ = v___x_2088_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(lean_object* v___x_2097_, lean_object* v_x_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2097_, v_x_2098_);
lean_dec_ref(v___x_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__17___boxed(lean_object* v___x_2100_, lean_object* v_sz_2101_, lean_object* v_i_2102_, lean_object* v_bs_2103_){
_start:
{
size_t v_sz_boxed_2104_; size_t v_i_boxed_2105_; lean_object* v_res_2106_; 
v_sz_boxed_2104_ = lean_unbox_usize(v_sz_2101_);
lean_dec(v_sz_2101_);
v_i_boxed_2105_ = lean_unbox_usize(v_i_2102_);
lean_dec(v_i_2102_);
v_res_2106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__17(v___x_2100_, v_sz_boxed_2104_, v_i_boxed_2105_, v_bs_2103_);
lean_dec_ref(v___x_2100_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object* v___x_2107_, lean_object* v_t_2108_){
_start:
{
lean_object* v_root_2109_; lean_object* v_tail_2110_; lean_object* v_size_2111_; size_t v_shift_2112_; lean_object* v_tailOff_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2124_; 
v_root_2109_ = lean_ctor_get(v_t_2108_, 0);
v_tail_2110_ = lean_ctor_get(v_t_2108_, 1);
v_size_2111_ = lean_ctor_get(v_t_2108_, 2);
v_shift_2112_ = lean_ctor_get_usize(v_t_2108_, 4);
v_tailOff_2113_ = lean_ctor_get(v_t_2108_, 3);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_t_2108_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2115_ = v_t_2108_;
v_isShared_2116_ = v_isSharedCheck_2124_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_tailOff_2113_);
lean_inc(v_size_2111_);
lean_inc(v_tail_2110_);
lean_inc(v_root_2109_);
lean_dec(v_t_2108_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2124_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; size_t v_sz_2118_; size_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2117_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2107_, v_root_2109_);
v_sz_2118_ = lean_array_size(v_tail_2110_);
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2107_, v_sz_2118_, v___x_2119_, v_tail_2110_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v___x_2120_);
lean_ctor_set(v___x_2115_, 0, v___x_2117_);
v___x_2122_ = v___x_2115_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_size_2111_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_tailOff_2113_);
lean_ctor_set_usize(v_reuseFailAlloc_2123_, 4, v_shift_2112_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object* v___x_2125_, lean_object* v_t_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2125_, v_t_2126_);
lean_dec_ref(v___x_2125_);
return v_res_2127_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_unsigned_to_nat(32u);
v___x_2129_ = lean_mk_empty_array_with_capacity(v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
return v___x_2130_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1(void){
_start:
{
size_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2131_ = ((size_t)5ULL);
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_unsigned_to_nat(32u);
v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
v___x_2135_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0);
v___x_2136_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2134_);
lean_ctor_set(v___x_2136_, 2, v___x_2132_);
lean_ctor_set(v___x_2136_, 3, v___x_2132_);
lean_ctor_set_usize(v___x_2136_, 4, v___x_2131_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_bs_2139_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2140_ == 0)
{
return v_bs_2139_;
}
else
{
lean_object* v___x_2141_; lean_object* v_bs_x27_2142_; lean_object* v___x_2143_; size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v_bs_x27_2142_ = lean_array_uset(v_bs_2139_, v_i_2138_, v___x_2141_);
v___x_2143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1);
v___x_2144_ = ((size_t)1ULL);
v___x_2145_ = lean_usize_add(v_i_2138_, v___x_2144_);
v___x_2146_ = lean_array_uset(v_bs_x27_2142_, v_i_2138_, v___x_2143_);
v_i_2138_ = v___x_2145_;
v_bs_2139_ = v___x_2146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(lean_object* v_sz_2148_, lean_object* v_i_2149_, lean_object* v_bs_2150_){
_start:
{
size_t v_sz_boxed_2151_; size_t v_i_boxed_2152_; lean_object* v_res_2153_; 
v_sz_boxed_2151_ = lean_unbox_usize(v_sz_2148_);
lean_dec(v_sz_2148_);
v_i_boxed_2152_ = lean_unbox_usize(v_i_2149_);
lean_dec(v_i_2149_);
v_res_2153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_boxed_2151_, v_i_boxed_2152_, v_bs_2150_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__13(size_t v_sz_2154_, size_t v_i_2155_, lean_object* v_bs_2156_){
_start:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_usize_dec_lt(v_i_2155_, v_sz_2154_);
if (v___x_2157_ == 0)
{
return v_bs_2156_;
}
else
{
lean_object* v_v_2158_; lean_object* v___x_2159_; lean_object* v_bs_x27_2160_; lean_object* v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
v_v_2158_ = lean_array_uget(v_bs_2156_, v_i_2155_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v_bs_x27_2160_ = lean_array_uset(v_bs_2156_, v_i_2155_, v___x_2159_);
v___x_2161_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_v_2158_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2155_, v___x_2162_);
v___x_2164_ = lean_array_uset(v_bs_x27_2160_, v_i_2155_, v___x_2161_);
v_i_2155_ = v___x_2163_;
v_bs_2156_ = v___x_2164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object* v_x_2166_){
_start:
{
if (lean_obj_tag(v_x_2166_) == 0)
{
lean_object* v_cs_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2177_; 
v_cs_2167_ = lean_ctor_get(v_x_2166_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_x_2166_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2169_ = v_x_2166_;
v_isShared_2170_ = v_isSharedCheck_2177_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_cs_2167_);
lean_dec(v_x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2177_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
size_t v_sz_2171_; size_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
v_sz_2171_ = lean_array_size(v_cs_2167_);
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__13(v_sz_2171_, v___x_2172_, v_cs_2167_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2173_);
v___x_2175_ = v___x_2169_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v_vs_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2188_; 
v_vs_2178_ = lean_ctor_get(v_x_2166_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_x_2166_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2180_ = v_x_2166_;
v_isShared_2181_ = v_isSharedCheck_2188_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_vs_2178_);
lean_dec(v_x_2166_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2188_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
size_t v_sz_2182_; size_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v_sz_2182_ = lean_array_size(v_vs_2178_);
v___x_2183_ = ((size_t)0ULL);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_2182_, v___x_2183_, v_vs_2178_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2184_);
v___x_2186_ = v___x_2180_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__13___boxed(lean_object* v_sz_2189_, lean_object* v_i_2190_, lean_object* v_bs_2191_){
_start:
{
size_t v_sz_boxed_2192_; size_t v_i_boxed_2193_; lean_object* v_res_2194_; 
v_sz_boxed_2192_ = lean_unbox_usize(v_sz_2189_);
lean_dec(v_sz_2189_);
v_i_boxed_2193_ = lean_unbox_usize(v_i_2190_);
lean_dec(v_i_2190_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__13(v_sz_boxed_2192_, v_i_boxed_2193_, v_bs_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object* v_t_2195_){
_start:
{
lean_object* v_root_2196_; lean_object* v_tail_2197_; lean_object* v_size_2198_; size_t v_shift_2199_; lean_object* v_tailOff_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2211_; 
v_root_2196_ = lean_ctor_get(v_t_2195_, 0);
v_tail_2197_ = lean_ctor_get(v_t_2195_, 1);
v_size_2198_ = lean_ctor_get(v_t_2195_, 2);
v_shift_2199_ = lean_ctor_get_usize(v_t_2195_, 4);
v_tailOff_2200_ = lean_ctor_get(v_t_2195_, 3);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_t_2195_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2202_ = v_t_2195_;
v_isShared_2203_ = v_isSharedCheck_2211_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_tailOff_2200_);
lean_inc(v_size_2198_);
lean_inc(v_tail_2197_);
lean_inc(v_root_2196_);
lean_dec(v_t_2195_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2211_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; size_t v_sz_2205_; size_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2204_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_root_2196_);
v_sz_2205_ = lean_array_size(v_tail_2197_);
v___x_2206_ = ((size_t)0ULL);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_2205_, v___x_2206_, v_tail_2197_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 1, v___x_2207_);
lean_ctor_set(v___x_2202_, 0, v___x_2204_);
v___x_2209_ = v___x_2202_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_size_2198_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_tailOff_2200_);
lean_ctor_set_usize(v_reuseFailAlloc_2210_, 4, v_shift_2199_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = lean_unsigned_to_nat(32u);
v___x_2213_ = lean_mk_empty_array_with_capacity(v___x_2212_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1(void){
_start:
{
size_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2215_ = ((size_t)5ULL);
v___x_2216_ = lean_unsigned_to_nat(0u);
v___x_2217_ = lean_unsigned_to_nat(32u);
v___x_2218_ = lean_mk_empty_array_with_capacity(v___x_2217_);
v___x_2219_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0);
v___x_2220_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___x_2218_);
lean_ctor_set(v___x_2220_, 2, v___x_2216_);
lean_ctor_set(v___x_2220_, 3, v___x_2216_);
lean_ctor_set_usize(v___x_2220_, 4, v___x_2215_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(size_t v_sz_2221_, size_t v_i_2222_, lean_object* v_bs_2223_){
_start:
{
uint8_t v___x_2224_; 
v___x_2224_ = lean_usize_dec_lt(v_i_2222_, v_sz_2221_);
if (v___x_2224_ == 0)
{
return v_bs_2223_;
}
else
{
lean_object* v___x_2225_; lean_object* v_bs_x27_2226_; lean_object* v___x_2227_; size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
v___x_2225_ = lean_unsigned_to_nat(0u);
v_bs_x27_2226_ = lean_array_uset(v_bs_2223_, v_i_2222_, v___x_2225_);
v___x_2227_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1);
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_add(v_i_2222_, v___x_2228_);
v___x_2230_ = lean_array_uset(v_bs_x27_2226_, v_i_2222_, v___x_2227_);
v_i_2222_ = v___x_2229_;
v_bs_2223_ = v___x_2230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(lean_object* v_sz_2232_, lean_object* v_i_2233_, lean_object* v_bs_2234_){
_start:
{
size_t v_sz_boxed_2235_; size_t v_i_boxed_2236_; lean_object* v_res_2237_; 
v_sz_boxed_2235_ = lean_unbox_usize(v_sz_2232_);
lean_dec(v_sz_2232_);
v_i_boxed_2236_ = lean_unbox_usize(v_i_2233_);
lean_dec(v_i_2233_);
v_res_2237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_boxed_2235_, v_i_boxed_2236_, v_bs_2234_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__9(size_t v_sz_2238_, size_t v_i_2239_, lean_object* v_bs_2240_){
_start:
{
uint8_t v___x_2241_; 
v___x_2241_ = lean_usize_dec_lt(v_i_2239_, v_sz_2238_);
if (v___x_2241_ == 0)
{
return v_bs_2240_;
}
else
{
lean_object* v_v_2242_; lean_object* v___x_2243_; lean_object* v_bs_x27_2244_; lean_object* v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; lean_object* v___x_2248_; 
v_v_2242_ = lean_array_uget(v_bs_2240_, v_i_2239_);
v___x_2243_ = lean_unsigned_to_nat(0u);
v_bs_x27_2244_ = lean_array_uset(v_bs_2240_, v_i_2239_, v___x_2243_);
v___x_2245_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_v_2242_);
v___x_2246_ = ((size_t)1ULL);
v___x_2247_ = lean_usize_add(v_i_2239_, v___x_2246_);
v___x_2248_ = lean_array_uset(v_bs_x27_2244_, v_i_2239_, v___x_2245_);
v_i_2239_ = v___x_2247_;
v_bs_2240_ = v___x_2248_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(lean_object* v_x_2250_){
_start:
{
if (lean_obj_tag(v_x_2250_) == 0)
{
lean_object* v_cs_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2261_; 
v_cs_2251_ = lean_ctor_get(v_x_2250_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_x_2250_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2253_ = v_x_2250_;
v_isShared_2254_ = v_isSharedCheck_2261_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_cs_2251_);
lean_dec(v_x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2261_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
size_t v_sz_2255_; size_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v_sz_2255_ = lean_array_size(v_cs_2251_);
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__9(v_sz_2255_, v___x_2256_, v_cs_2251_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2257_);
v___x_2259_ = v___x_2253_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_vs_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2272_; 
v_vs_2262_ = lean_ctor_get(v_x_2250_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_x_2250_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2264_ = v_x_2250_;
v_isShared_2265_ = v_isSharedCheck_2272_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_vs_2262_);
lean_dec(v_x_2250_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2272_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
size_t v_sz_2266_; size_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v_sz_2266_ = lean_array_size(v_vs_2262_);
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_2266_, v___x_2267_, v_vs_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2268_);
v___x_2270_ = v___x_2264_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__9___boxed(lean_object* v_sz_2273_, lean_object* v_i_2274_, lean_object* v_bs_2275_){
_start:
{
size_t v_sz_boxed_2276_; size_t v_i_boxed_2277_; lean_object* v_res_2278_; 
v_sz_boxed_2276_ = lean_unbox_usize(v_sz_2273_);
lean_dec(v_sz_2273_);
v_i_boxed_2277_ = lean_unbox_usize(v_i_2274_);
lean_dec(v_i_2274_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__9(v_sz_boxed_2276_, v_i_boxed_2277_, v_bs_2275_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object* v_t_2279_){
_start:
{
lean_object* v_root_2280_; lean_object* v_tail_2281_; lean_object* v_size_2282_; size_t v_shift_2283_; lean_object* v_tailOff_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2295_; 
v_root_2280_ = lean_ctor_get(v_t_2279_, 0);
v_tail_2281_ = lean_ctor_get(v_t_2279_, 1);
v_size_2282_ = lean_ctor_get(v_t_2279_, 2);
v_shift_2283_ = lean_ctor_get_usize(v_t_2279_, 4);
v_tailOff_2284_ = lean_ctor_get(v_t_2279_, 3);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_t_2279_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2286_ = v_t_2279_;
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_tailOff_2284_);
lean_inc(v_size_2282_);
lean_inc(v_tail_2281_);
lean_inc(v_root_2280_);
lean_dec(v_t_2279_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; size_t v_sz_2289_; size_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2288_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_root_2280_);
v_sz_2289_ = lean_array_size(v_tail_2281_);
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_2289_, v___x_2290_, v_tail_2281_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 1, v___x_2291_);
lean_ctor_set(v___x_2286_, 0, v___x_2288_);
v___x_2293_ = v___x_2286_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_size_2282_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_tailOff_2284_);
lean_ctor_set_usize(v_reuseFailAlloc_2294_, 4, v_shift_2283_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(size_t v_sz_2296_, size_t v_i_2297_, lean_object* v_bs_2298_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_usize_dec_lt(v_i_2297_, v_sz_2296_);
if (v___x_2299_ == 0)
{
return v_bs_2298_;
}
else
{
lean_object* v___x_2300_; lean_object* v_bs_x27_2301_; lean_object* v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v_bs_x27_2301_ = lean_array_uset(v_bs_2298_, v_i_2297_, v___x_2300_);
v___x_2302_ = lean_box(1);
v___x_2303_ = ((size_t)1ULL);
v___x_2304_ = lean_usize_add(v_i_2297_, v___x_2303_);
v___x_2305_ = lean_array_uset(v_bs_x27_2301_, v_i_2297_, v___x_2302_);
v_i_2297_ = v___x_2304_;
v_bs_2298_ = v___x_2305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(lean_object* v_sz_2307_, lean_object* v_i_2308_, lean_object* v_bs_2309_){
_start:
{
size_t v_sz_boxed_2310_; size_t v_i_boxed_2311_; lean_object* v_res_2312_; 
v_sz_boxed_2310_ = lean_unbox_usize(v_sz_2307_);
lean_dec(v_sz_2307_);
v_i_boxed_2311_ = lean_unbox_usize(v_i_2308_);
lean_dec(v_i_2308_);
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_boxed_2310_, v_i_boxed_2311_, v_bs_2309_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__22(size_t v_sz_2313_, size_t v_i_2314_, lean_object* v_bs_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_usize_dec_lt(v_i_2314_, v_sz_2313_);
if (v___x_2316_ == 0)
{
return v_bs_2315_;
}
else
{
lean_object* v_v_2317_; lean_object* v___x_2318_; lean_object* v_bs_x27_2319_; lean_object* v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v_v_2317_ = lean_array_uget(v_bs_2315_, v_i_2314_);
v___x_2318_ = lean_unsigned_to_nat(0u);
v_bs_x27_2319_ = lean_array_uset(v_bs_2315_, v_i_2314_, v___x_2318_);
v___x_2320_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_v_2317_);
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_add(v_i_2314_, v___x_2321_);
v___x_2323_ = lean_array_uset(v_bs_x27_2319_, v_i_2314_, v___x_2320_);
v_i_2314_ = v___x_2322_;
v_bs_2315_ = v___x_2323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(lean_object* v_x_2325_){
_start:
{
if (lean_obj_tag(v_x_2325_) == 0)
{
lean_object* v_cs_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2336_; 
v_cs_2326_ = lean_ctor_get(v_x_2325_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_x_2325_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2328_ = v_x_2325_;
v_isShared_2329_ = v_isSharedCheck_2336_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_cs_2326_);
lean_dec(v_x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2336_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
size_t v_sz_2330_; size_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v_sz_2330_ = lean_array_size(v_cs_2326_);
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__22(v_sz_2330_, v___x_2331_, v_cs_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2332_);
v___x_2334_ = v___x_2328_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
else
{
lean_object* v_vs_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2347_; 
v_vs_2337_ = lean_ctor_get(v_x_2325_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_x_2325_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2339_ = v_x_2325_;
v_isShared_2340_ = v_isSharedCheck_2347_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_vs_2337_);
lean_dec(v_x_2325_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2347_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
size_t v_sz_2341_; size_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v_sz_2341_ = lean_array_size(v_vs_2337_);
v___x_2342_ = ((size_t)0ULL);
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_2341_, v___x_2342_, v_vs_2337_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2343_);
v___x_2345_ = v___x_2339_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__22___boxed(lean_object* v_sz_2348_, lean_object* v_i_2349_, lean_object* v_bs_2350_){
_start:
{
size_t v_sz_boxed_2351_; size_t v_i_boxed_2352_; lean_object* v_res_2353_; 
v_sz_boxed_2351_ = lean_unbox_usize(v_sz_2348_);
lean_dec(v_sz_2348_);
v_i_boxed_2352_ = lean_unbox_usize(v_i_2349_);
lean_dec(v_i_2349_);
v_res_2353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__22(v_sz_boxed_2351_, v_i_boxed_2352_, v_bs_2350_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object* v_t_2354_){
_start:
{
lean_object* v_root_2355_; lean_object* v_tail_2356_; lean_object* v_size_2357_; size_t v_shift_2358_; lean_object* v_tailOff_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2370_; 
v_root_2355_ = lean_ctor_get(v_t_2354_, 0);
v_tail_2356_ = lean_ctor_get(v_t_2354_, 1);
v_size_2357_ = lean_ctor_get(v_t_2354_, 2);
v_shift_2358_ = lean_ctor_get_usize(v_t_2354_, 4);
v_tailOff_2359_ = lean_ctor_get(v_t_2354_, 3);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_t_2354_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2361_ = v_t_2354_;
v_isShared_2362_ = v_isSharedCheck_2370_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_tailOff_2359_);
lean_inc(v_size_2357_);
lean_inc(v_tail_2356_);
lean_inc(v_root_2355_);
lean_dec(v_t_2354_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2370_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; size_t v_sz_2364_; size_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2363_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_root_2355_);
v_sz_2364_ = lean_array_size(v_tail_2356_);
v___x_2365_ = ((size_t)0ULL);
v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_2364_, v___x_2365_, v_tail_2356_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 1, v___x_2366_);
lean_ctor_set(v___x_2361_, 0, v___x_2363_);
v___x_2368_ = v___x_2361_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_size_2357_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v_tailOff_2359_);
lean_ctor_set_usize(v_reuseFailAlloc_2369_, 4, v_shift_2358_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object* v___x_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
if (lean_obj_tag(v_a_2372_) == 0)
{
lean_object* v___x_2374_; 
v___x_2374_ = l_List_reverse___redArg(v_a_2373_);
return v___x_2374_;
}
else
{
lean_object* v_head_2375_; lean_object* v_tail_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2386_; 
v_head_2375_ = lean_ctor_get(v_a_2372_, 0);
v_tail_2376_ = lean_ctor_get(v_a_2372_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_a_2372_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2378_ = v_a_2372_;
v_isShared_2379_ = v_isSharedCheck_2386_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_tail_2376_);
lean_inc(v_head_2375_);
lean_dec(v_a_2372_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2386_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = lean_array_get_borrowed(v___x_2380_, v___x_2371_, v_head_2375_);
lean_dec(v_head_2375_);
lean_inc(v___x_2381_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 1, v_a_2373_);
lean_ctor_set(v___x_2378_, 0, v___x_2381_);
v___x_2383_ = v___x_2378_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2373_);
v___x_2383_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
v_a_2372_ = v_tail_2376_;
v_a_2373_ = v___x_2383_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object* v___x_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2387_, v_a_2388_, v_a_2389_);
lean_dec_ref(v___x_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(size_t v_sz_2391_, size_t v_i_2392_, lean_object* v_bs_2393_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_usize_dec_lt(v_i_2392_, v_sz_2391_);
if (v___x_2394_ == 0)
{
return v_bs_2393_;
}
else
{
lean_object* v___x_2395_; lean_object* v_bs_x27_2396_; lean_object* v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2395_ = lean_unsigned_to_nat(0u);
v_bs_x27_2396_ = lean_array_uset(v_bs_2393_, v_i_2392_, v___x_2395_);
v___x_2397_ = lean_box(0);
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_add(v_i_2392_, v___x_2398_);
v___x_2400_ = lean_array_uset(v_bs_x27_2396_, v_i_2392_, v___x_2397_);
v_i_2392_ = v___x_2399_;
v_bs_2393_ = v___x_2400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object* v_sz_2402_, lean_object* v_i_2403_, lean_object* v_bs_2404_){
_start:
{
size_t v_sz_boxed_2405_; size_t v_i_boxed_2406_; lean_object* v_res_2407_; 
v_sz_boxed_2405_ = lean_unbox_usize(v_sz_2402_);
lean_dec(v_sz_2402_);
v_i_boxed_2406_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_boxed_2405_, v_i_boxed_2406_, v_bs_2404_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__5(size_t v_sz_2408_, size_t v_i_2409_, lean_object* v_bs_2410_){
_start:
{
uint8_t v___x_2411_; 
v___x_2411_ = lean_usize_dec_lt(v_i_2409_, v_sz_2408_);
if (v___x_2411_ == 0)
{
return v_bs_2410_;
}
else
{
lean_object* v_v_2412_; lean_object* v___x_2413_; lean_object* v_bs_x27_2414_; lean_object* v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v_v_2412_ = lean_array_uget(v_bs_2410_, v_i_2409_);
v___x_2413_ = lean_unsigned_to_nat(0u);
v_bs_x27_2414_ = lean_array_uset(v_bs_2410_, v_i_2409_, v___x_2413_);
v___x_2415_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_v_2412_);
v___x_2416_ = ((size_t)1ULL);
v___x_2417_ = lean_usize_add(v_i_2409_, v___x_2416_);
v___x_2418_ = lean_array_uset(v_bs_x27_2414_, v_i_2409_, v___x_2415_);
v_i_2409_ = v___x_2417_;
v_bs_2410_ = v___x_2418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object* v_x_2420_){
_start:
{
if (lean_obj_tag(v_x_2420_) == 0)
{
lean_object* v_cs_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2431_; 
v_cs_2421_ = lean_ctor_get(v_x_2420_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_x_2420_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2423_ = v_x_2420_;
v_isShared_2424_ = v_isSharedCheck_2431_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_cs_2421_);
lean_dec(v_x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2431_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
size_t v_sz_2425_; size_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v_sz_2425_ = lean_array_size(v_cs_2421_);
v___x_2426_ = ((size_t)0ULL);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__5(v_sz_2425_, v___x_2426_, v_cs_2421_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2427_);
v___x_2429_ = v___x_2423_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
else
{
lean_object* v_vs_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2442_; 
v_vs_2432_ = lean_ctor_get(v_x_2420_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_x_2420_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2434_ = v_x_2420_;
v_isShared_2435_ = v_isSharedCheck_2442_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_vs_2432_);
lean_dec(v_x_2420_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2442_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
size_t v_sz_2436_; size_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v_sz_2436_ = lean_array_size(v_vs_2432_);
v___x_2437_ = ((size_t)0ULL);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_2436_, v___x_2437_, v_vs_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2438_);
v___x_2440_ = v___x_2434_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_2443_, lean_object* v_i_2444_, lean_object* v_bs_2445_){
_start:
{
size_t v_sz_boxed_2446_; size_t v_i_boxed_2447_; lean_object* v_res_2448_; 
v_sz_boxed_2446_ = lean_unbox_usize(v_sz_2443_);
lean_dec(v_sz_2443_);
v_i_boxed_2447_ = lean_unbox_usize(v_i_2444_);
lean_dec(v_i_2444_);
v_res_2448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__5(v_sz_boxed_2446_, v_i_boxed_2447_, v_bs_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object* v_t_2449_){
_start:
{
lean_object* v_root_2450_; lean_object* v_tail_2451_; lean_object* v_size_2452_; size_t v_shift_2453_; lean_object* v_tailOff_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2465_; 
v_root_2450_ = lean_ctor_get(v_t_2449_, 0);
v_tail_2451_ = lean_ctor_get(v_t_2449_, 1);
v_size_2452_ = lean_ctor_get(v_t_2449_, 2);
v_shift_2453_ = lean_ctor_get_usize(v_t_2449_, 4);
v_tailOff_2454_ = lean_ctor_get(v_t_2449_, 3);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_t_2449_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2456_ = v_t_2449_;
v_isShared_2457_ = v_isSharedCheck_2465_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_tailOff_2454_);
lean_inc(v_size_2452_);
lean_inc(v_tail_2451_);
lean_inc(v_root_2450_);
lean_dec(v_t_2449_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2465_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; size_t v_sz_2459_; size_t v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2458_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_root_2450_);
v_sz_2459_ = lean_array_size(v_tail_2451_);
v___x_2460_ = ((size_t)0ULL);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_2459_, v___x_2460_, v_tail_2451_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 1, v___x_2461_);
lean_ctor_set(v___x_2456_, 0, v___x_2458_);
v___x_2463_ = v___x_2456_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v_size_2452_);
lean_ctor_set(v_reuseFailAlloc_2464_, 3, v_tailOff_2454_);
lean_ctor_set_usize(v_reuseFailAlloc_2464_, 4, v_shift_2453_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object* v_a_2466_, lean_object* v___f_2467_, lean_object* v___x_2468_, lean_object* v_s_2469_){
_start:
{
lean_object* v_vars_2470_; lean_object* v_varMap_2471_; lean_object* v_natToIntMap_2472_; lean_object* v_natDef_2473_; lean_object* v_dvds_2474_; lean_object* v_lowers_2475_; lean_object* v_uppers_2476_; lean_object* v_diseqs_2477_; lean_object* v_elimEqs_2478_; lean_object* v_elimStack_2479_; lean_object* v_occurs_2480_; lean_object* v_assignment_2481_; lean_object* v_nextCnstrId_2482_; uint8_t v_caseSplits_2483_; lean_object* v_conflict_x3f_2484_; lean_object* v_divMod_2485_; lean_object* v_toIntIds_2486_; lean_object* v_toIntInfos_2487_; lean_object* v_toIntTermMap_2488_; lean_object* v_toIntVarMap_2489_; uint8_t v_usedCommRing_2490_; lean_object* v_nonlinearOccs_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2513_; 
v_vars_2470_ = lean_ctor_get(v_s_2469_, 0);
v_varMap_2471_ = lean_ctor_get(v_s_2469_, 1);
v_natToIntMap_2472_ = lean_ctor_get(v_s_2469_, 4);
v_natDef_2473_ = lean_ctor_get(v_s_2469_, 5);
v_dvds_2474_ = lean_ctor_get(v_s_2469_, 6);
v_lowers_2475_ = lean_ctor_get(v_s_2469_, 7);
v_uppers_2476_ = lean_ctor_get(v_s_2469_, 8);
v_diseqs_2477_ = lean_ctor_get(v_s_2469_, 9);
v_elimEqs_2478_ = lean_ctor_get(v_s_2469_, 10);
v_elimStack_2479_ = lean_ctor_get(v_s_2469_, 11);
v_occurs_2480_ = lean_ctor_get(v_s_2469_, 12);
v_assignment_2481_ = lean_ctor_get(v_s_2469_, 13);
v_nextCnstrId_2482_ = lean_ctor_get(v_s_2469_, 14);
v_caseSplits_2483_ = lean_ctor_get_uint8(v_s_2469_, sizeof(void*)*23);
v_conflict_x3f_2484_ = lean_ctor_get(v_s_2469_, 15);
v_divMod_2485_ = lean_ctor_get(v_s_2469_, 17);
v_toIntIds_2486_ = lean_ctor_get(v_s_2469_, 18);
v_toIntInfos_2487_ = lean_ctor_get(v_s_2469_, 19);
v_toIntTermMap_2488_ = lean_ctor_get(v_s_2469_, 20);
v_toIntVarMap_2489_ = lean_ctor_get(v_s_2469_, 21);
v_usedCommRing_2490_ = lean_ctor_get_uint8(v_s_2469_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2491_ = lean_ctor_get(v_s_2469_, 22);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_s_2469_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; lean_object* v_unused_2515_; lean_object* v_unused_2516_; 
v_unused_2514_ = lean_ctor_get(v_s_2469_, 16);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_s_2469_, 3);
lean_dec(v_unused_2515_);
v_unused_2516_ = lean_ctor_get(v_s_2469_, 2);
lean_dec(v_unused_2516_);
v___x_2493_ = v_s_2469_;
v_isShared_2494_ = v_isSharedCheck_2513_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_nonlinearOccs_2491_);
lean_inc(v_toIntVarMap_2489_);
lean_inc(v_toIntTermMap_2488_);
lean_inc(v_toIntInfos_2487_);
lean_inc(v_toIntIds_2486_);
lean_inc(v_divMod_2485_);
lean_inc(v_conflict_x3f_2484_);
lean_inc(v_nextCnstrId_2482_);
lean_inc(v_assignment_2481_);
lean_inc(v_occurs_2480_);
lean_inc(v_elimStack_2479_);
lean_inc(v_elimEqs_2478_);
lean_inc(v_diseqs_2477_);
lean_inc(v_uppers_2476_);
lean_inc(v_lowers_2475_);
lean_inc(v_dvds_2474_);
lean_inc(v_natDef_2473_);
lean_inc(v_natToIntMap_2472_);
lean_inc(v_varMap_2471_);
lean_inc(v_vars_2470_);
lean_dec(v_s_2469_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2513_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2495_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_a_2466_);
lean_inc_ref(v_vars_2470_);
v___x_2496_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2495_, v_vars_2470_, v_a_2466_);
lean_inc_ref(v___f_2467_);
lean_inc_ref(v_varMap_2471_);
v___x_2497_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_varMap_2471_, v___f_2467_);
v___x_2498_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_natDef_2473_, v___f_2467_);
v___x_2499_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(v_dvds_2474_);
v___x_2500_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_lowers_2475_);
v___x_2501_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_uppers_2476_);
v___x_2502_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_diseqs_2477_);
v___x_2503_ = lean_box(0);
v___x_2504_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2503_, v_elimEqs_2478_, v_a_2466_);
v___x_2505_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2468_, v___x_2504_);
v___x_2506_ = lean_box(0);
v___x_2507_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2468_, v_elimStack_2479_, v___x_2506_);
v___x_2508_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v_occurs_2480_);
v___x_2509_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 16, v___x_2509_);
lean_ctor_set(v___x_2493_, 12, v___x_2508_);
lean_ctor_set(v___x_2493_, 11, v___x_2507_);
lean_ctor_set(v___x_2493_, 10, v___x_2505_);
lean_ctor_set(v___x_2493_, 9, v___x_2502_);
lean_ctor_set(v___x_2493_, 8, v___x_2501_);
lean_ctor_set(v___x_2493_, 7, v___x_2500_);
lean_ctor_set(v___x_2493_, 6, v___x_2499_);
lean_ctor_set(v___x_2493_, 5, v___x_2498_);
lean_ctor_set(v___x_2493_, 3, v_varMap_2471_);
lean_ctor_set(v___x_2493_, 2, v_vars_2470_);
lean_ctor_set(v___x_2493_, 1, v___x_2497_);
lean_ctor_set(v___x_2493_, 0, v___x_2496_);
v___x_2511_ = v___x_2493_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_vars_2470_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_varMap_2471_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_natToIntMap_2472_);
lean_ctor_set(v_reuseFailAlloc_2512_, 5, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2512_, 6, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2512_, 7, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2512_, 8, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2512_, 9, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2512_, 10, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2512_, 11, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2512_, 12, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2512_, 13, v_assignment_2481_);
lean_ctor_set(v_reuseFailAlloc_2512_, 14, v_nextCnstrId_2482_);
lean_ctor_set(v_reuseFailAlloc_2512_, 15, v_conflict_x3f_2484_);
lean_ctor_set(v_reuseFailAlloc_2512_, 16, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2512_, 17, v_divMod_2485_);
lean_ctor_set(v_reuseFailAlloc_2512_, 18, v_toIntIds_2486_);
lean_ctor_set(v_reuseFailAlloc_2512_, 19, v_toIntInfos_2487_);
lean_ctor_set(v_reuseFailAlloc_2512_, 20, v_toIntTermMap_2488_);
lean_ctor_set(v_reuseFailAlloc_2512_, 21, v_toIntVarMap_2489_);
lean_ctor_set(v_reuseFailAlloc_2512_, 22, v_nonlinearOccs_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*23, v_caseSplits_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*23 + 1, v_usedCommRing_2490_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object* v_a_2517_, lean_object* v___f_2518_, lean_object* v___x_2519_, lean_object* v_s_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(v_a_2517_, v___f_2518_, v___x_2519_, v_s_2520_);
lean_dec_ref(v___x_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(lean_object* v_as_2522_, size_t v_i_2523_, size_t v_stop_2524_, lean_object* v_b_2525_){
_start:
{
lean_object* v___y_2527_; uint8_t v___x_2531_; 
v___x_2531_ = lean_usize_dec_eq(v_i_2523_, v_stop_2524_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_array_uget_borrowed(v_as_2522_, v_i_2523_);
if (lean_obj_tag(v___x_2532_) == 0)
{
v___y_2527_ = v_b_2525_;
goto v___jp_2526_;
}
else
{
lean_object* v_val_2533_; lean_object* v___x_2534_; 
v_val_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_val_2533_);
v___x_2534_ = lean_array_push(v_b_2525_, v_val_2533_);
v___y_2527_ = v___x_2534_;
goto v___jp_2526_;
}
}
else
{
return v_b_2525_;
}
v___jp_2526_:
{
size_t v___x_2528_; size_t v___x_2529_; 
v___x_2528_ = ((size_t)1ULL);
v___x_2529_ = lean_usize_add(v_i_2523_, v___x_2528_);
v_i_2523_ = v___x_2529_;
v_b_2525_ = v___y_2527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(lean_object* v_as_2535_, lean_object* v_i_2536_, lean_object* v_stop_2537_, lean_object* v_b_2538_){
_start:
{
size_t v_i_boxed_2539_; size_t v_stop_boxed_2540_; lean_object* v_res_2541_; 
v_i_boxed_2539_ = lean_unbox_usize(v_i_2536_);
lean_dec(v_i_2536_);
v_stop_boxed_2540_ = lean_unbox_usize(v_stop_2537_);
lean_dec(v_stop_2537_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_as_2535_, v_i_boxed_2539_, v_stop_boxed_2540_, v_b_2538_);
lean_dec_ref(v_as_2535_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
if (lean_obj_tag(v_x_2542_) == 0)
{
lean_object* v_cs_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_cs_2544_ = lean_ctor_get(v_x_2542_, 0);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_array_get_size(v_cs_2544_);
v___x_2547_ = lean_nat_dec_lt(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
return v_x_2543_;
}
else
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_nat_dec_le(v___x_2546_, v___x_2546_);
if (v___x_2548_ == 0)
{
if (v___x_2547_ == 0)
{
return v_x_2543_;
}
else
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = lean_usize_of_nat(v___x_2546_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26(v_cs_2544_, v___x_2549_, v___x_2550_, v_x_2543_);
return v___x_2551_;
}
}
else
{
size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = lean_usize_of_nat(v___x_2546_);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26(v_cs_2544_, v___x_2552_, v___x_2553_, v_x_2543_);
return v___x_2554_;
}
}
}
else
{
lean_object* v_vs_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v_vs_2555_ = lean_ctor_get(v_x_2542_, 0);
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = lean_array_get_size(v_vs_2555_);
v___x_2558_ = lean_nat_dec_lt(v___x_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
return v_x_2543_;
}
else
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_nat_dec_le(v___x_2557_, v___x_2557_);
if (v___x_2559_ == 0)
{
if (v___x_2558_ == 0)
{
return v_x_2543_;
}
else
{
size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = lean_usize_of_nat(v___x_2557_);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2555_, v___x_2560_, v___x_2561_, v_x_2543_);
return v___x_2562_;
}
}
else
{
size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((size_t)0ULL);
v___x_2564_ = lean_usize_of_nat(v___x_2557_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2555_, v___x_2563_, v___x_2564_, v_x_2543_);
return v___x_2565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26(lean_object* v_as_2566_, size_t v_i_2567_, size_t v_stop_2568_, lean_object* v_b_2569_){
_start:
{
uint8_t v___x_2570_; 
v___x_2570_ = lean_usize_dec_eq(v_i_2567_, v_stop_2568_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; size_t v___x_2573_; size_t v___x_2574_; 
v___x_2571_ = lean_array_uget_borrowed(v_as_2566_, v_i_2567_);
v___x_2572_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v___x_2571_, v_b_2569_);
v___x_2573_ = ((size_t)1ULL);
v___x_2574_ = lean_usize_add(v_i_2567_, v___x_2573_);
v_i_2567_ = v___x_2574_;
v_b_2569_ = v___x_2572_;
goto _start;
}
else
{
return v_b_2569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26___boxed(lean_object* v_as_2576_, lean_object* v_i_2577_, lean_object* v_stop_2578_, lean_object* v_b_2579_){
_start:
{
size_t v_i_boxed_2580_; size_t v_stop_boxed_2581_; lean_object* v_res_2582_; 
v_i_boxed_2580_ = lean_unbox_usize(v_i_2577_);
lean_dec(v_i_2577_);
v_stop_boxed_2581_ = lean_unbox_usize(v_stop_2578_);
lean_dec(v_stop_2578_);
v_res_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26(v_as_2576_, v_i_boxed_2580_, v_stop_boxed_2581_, v_b_2579_);
lean_dec_ref(v_as_2576_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20___boxed(lean_object* v_x_2583_, lean_object* v_x_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_x_2583_, v_x_2584_);
lean_dec_ref(v_x_2583_);
return v_res_2585_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(lean_object* v_x_2587_, size_t v_x_2588_, size_t v_x_2589_, lean_object* v_x_2590_){
_start:
{
if (lean_obj_tag(v_x_2587_) == 0)
{
lean_object* v_cs_2591_; lean_object* v___x_2592_; size_t v___x_2593_; lean_object* v_j_2594_; lean_object* v___x_2595_; size_t v___x_2596_; size_t v___x_2597_; size_t v___x_2598_; size_t v___x_2599_; size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v_cs_2591_ = lean_ctor_get(v_x_2587_, 0);
v___x_2592_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_2593_ = lean_usize_shift_right(v_x_2588_, v_x_2589_);
v_j_2594_ = lean_usize_to_nat(v___x_2593_);
v___x_2595_ = lean_array_get_borrowed(v___x_2592_, v_cs_2591_, v_j_2594_);
v___x_2596_ = ((size_t)1ULL);
v___x_2597_ = lean_usize_shift_left(v___x_2596_, v_x_2589_);
v___x_2598_ = lean_usize_sub(v___x_2597_, v___x_2596_);
v___x_2599_ = lean_usize_land(v_x_2588_, v___x_2598_);
v___x_2600_ = ((size_t)5ULL);
v___x_2601_ = lean_usize_sub(v_x_2589_, v___x_2600_);
v___x_2602_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v___x_2595_, v___x_2599_, v___x_2601_, v_x_2590_);
v___x_2603_ = lean_unsigned_to_nat(1u);
v___x_2604_ = lean_nat_add(v_j_2594_, v___x_2603_);
lean_dec(v_j_2594_);
v___x_2605_ = lean_array_get_size(v_cs_2591_);
v___x_2606_ = lean_nat_dec_lt(v___x_2604_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_dec(v___x_2604_);
return v___x_2602_;
}
else
{
uint8_t v___x_2607_; 
v___x_2607_ = lean_nat_dec_le(v___x_2605_, v___x_2605_);
if (v___x_2607_ == 0)
{
if (v___x_2606_ == 0)
{
lean_dec(v___x_2604_);
return v___x_2602_;
}
else
{
size_t v___x_2608_; size_t v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_usize_of_nat(v___x_2604_);
lean_dec(v___x_2604_);
v___x_2609_ = lean_usize_of_nat(v___x_2605_);
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26(v_cs_2591_, v___x_2608_, v___x_2609_, v___x_2602_);
return v___x_2610_;
}
}
else
{
size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_usize_of_nat(v___x_2604_);
lean_dec(v___x_2604_);
v___x_2612_ = lean_usize_of_nat(v___x_2605_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__26(v_cs_2591_, v___x_2611_, v___x_2612_, v___x_2602_);
return v___x_2613_;
}
}
}
else
{
lean_object* v_vs_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v_vs_2614_ = lean_ctor_get(v_x_2587_, 0);
v___x_2615_ = lean_usize_to_nat(v_x_2588_);
v___x_2616_ = lean_array_get_size(v_vs_2614_);
v___x_2617_ = lean_nat_dec_lt(v___x_2615_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_dec(v___x_2615_);
return v_x_2590_;
}
else
{
uint8_t v___x_2618_; 
v___x_2618_ = lean_nat_dec_le(v___x_2616_, v___x_2616_);
if (v___x_2618_ == 0)
{
if (v___x_2617_ == 0)
{
lean_dec(v___x_2615_);
return v_x_2590_;
}
else
{
size_t v___x_2619_; size_t v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = lean_usize_of_nat(v___x_2615_);
lean_dec(v___x_2615_);
v___x_2620_ = lean_usize_of_nat(v___x_2616_);
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2614_, v___x_2619_, v___x_2620_, v_x_2590_);
return v___x_2621_;
}
}
else
{
size_t v___x_2622_; size_t v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_usize_of_nat(v___x_2615_);
lean_dec(v___x_2615_);
v___x_2623_ = lean_usize_of_nat(v___x_2616_);
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2614_, v___x_2622_, v___x_2623_, v_x_2590_);
return v___x_2624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___boxed(lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_, lean_object* v_x_2628_){
_start:
{
size_t v_x_86479__boxed_2629_; size_t v_x_86480__boxed_2630_; lean_object* v_res_2631_; 
v_x_86479__boxed_2629_ = lean_unbox_usize(v_x_2626_);
lean_dec(v_x_2626_);
v_x_86480__boxed_2630_ = lean_unbox_usize(v_x_2627_);
lean_dec(v_x_2627_);
v_res_2631_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_x_2625_, v_x_86479__boxed_2629_, v_x_86480__boxed_2630_, v_x_2628_);
lean_dec_ref(v_x_2625_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object* v_t_2632_, lean_object* v_init_2633_, lean_object* v_start_2634_){
_start:
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = lean_nat_dec_eq(v_start_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_object* v_root_2637_; lean_object* v_tail_2638_; size_t v_shift_2639_; lean_object* v_tailOff_2640_; uint8_t v___x_2641_; 
v_root_2637_ = lean_ctor_get(v_t_2632_, 0);
v_tail_2638_ = lean_ctor_get(v_t_2632_, 1);
v_shift_2639_ = lean_ctor_get_usize(v_t_2632_, 4);
v_tailOff_2640_ = lean_ctor_get(v_t_2632_, 3);
v___x_2641_ = lean_nat_dec_le(v_tailOff_2640_, v_start_2634_);
if (v___x_2641_ == 0)
{
size_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2642_ = lean_usize_of_nat(v_start_2634_);
v___x_2643_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_root_2637_, v___x_2642_, v_shift_2639_, v_init_2633_);
v___x_2644_ = lean_array_get_size(v_tail_2638_);
v___x_2645_ = lean_nat_dec_lt(v___x_2635_, v___x_2644_);
if (v___x_2645_ == 0)
{
return v___x_2643_;
}
else
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_nat_dec_le(v___x_2644_, v___x_2644_);
if (v___x_2646_ == 0)
{
if (v___x_2645_ == 0)
{
return v___x_2643_;
}
else
{
size_t v___x_2647_; size_t v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = ((size_t)0ULL);
v___x_2648_ = lean_usize_of_nat(v___x_2644_);
v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2638_, v___x_2647_, v___x_2648_, v___x_2643_);
return v___x_2649_;
}
}
else
{
size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = ((size_t)0ULL);
v___x_2651_ = lean_usize_of_nat(v___x_2644_);
v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2638_, v___x_2650_, v___x_2651_, v___x_2643_);
return v___x_2652_;
}
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = lean_nat_sub(v_start_2634_, v_tailOff_2640_);
v___x_2654_ = lean_array_get_size(v_tail_2638_);
v___x_2655_ = lean_nat_dec_lt(v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_dec(v___x_2653_);
return v_init_2633_;
}
else
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_nat_dec_le(v___x_2654_, v___x_2654_);
if (v___x_2656_ == 0)
{
if (v___x_2655_ == 0)
{
lean_dec(v___x_2653_);
return v_init_2633_;
}
else
{
size_t v___x_2657_; size_t v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_usize_of_nat(v___x_2653_);
lean_dec(v___x_2653_);
v___x_2658_ = lean_usize_of_nat(v___x_2654_);
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2638_, v___x_2657_, v___x_2658_, v_init_2633_);
return v___x_2659_;
}
}
else
{
size_t v___x_2660_; size_t v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_usize_of_nat(v___x_2653_);
lean_dec(v___x_2653_);
v___x_2661_ = lean_usize_of_nat(v___x_2654_);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2638_, v___x_2660_, v___x_2661_, v_init_2633_);
return v___x_2662_;
}
}
}
}
else
{
lean_object* v_root_2663_; lean_object* v_tail_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v_root_2663_ = lean_ctor_get(v_t_2632_, 0);
v_tail_2664_ = lean_ctor_get(v_t_2632_, 1);
v___x_2665_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_root_2663_, v_init_2633_);
v___x_2666_ = lean_array_get_size(v_tail_2664_);
v___x_2667_ = lean_nat_dec_lt(v___x_2635_, v___x_2666_);
if (v___x_2667_ == 0)
{
return v___x_2665_;
}
else
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_nat_dec_le(v___x_2666_, v___x_2666_);
if (v___x_2668_ == 0)
{
if (v___x_2667_ == 0)
{
return v___x_2665_;
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2666_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2664_, v___x_2669_, v___x_2670_, v___x_2665_);
return v___x_2671_;
}
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2666_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2664_, v___x_2672_, v___x_2673_, v___x_2665_);
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___boxed(lean_object* v_t_2675_, lean_object* v_init_2676_, lean_object* v_start_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_t_2675_, v_init_2676_, v_start_2677_);
lean_dec(v_start_2677_);
lean_dec_ref(v_t_2675_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(lean_object* v_as_2679_, size_t v_i_2680_, size_t v_stop_2681_, lean_object* v_b_2682_){
_start:
{
uint8_t v___x_2683_; 
v___x_2683_ = lean_usize_dec_eq(v_i_2680_, v_stop_2681_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; size_t v___x_2687_; size_t v___x_2688_; 
v___x_2684_ = lean_array_uget_borrowed(v_as_2679_, v_i_2680_);
v___x_2685_ = l_Lean_PersistentArray_toArray___redArg(v___x_2684_);
v___x_2686_ = l_Array_append___redArg(v_b_2682_, v___x_2685_);
lean_dec_ref(v___x_2685_);
v___x_2687_ = ((size_t)1ULL);
v___x_2688_ = lean_usize_add(v_i_2680_, v___x_2687_);
v_i_2680_ = v___x_2688_;
v_b_2682_ = v___x_2686_;
goto _start;
}
else
{
return v_b_2682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23___boxed(lean_object* v_as_2690_, lean_object* v_i_2691_, lean_object* v_stop_2692_, lean_object* v_b_2693_){
_start:
{
size_t v_i_boxed_2694_; size_t v_stop_boxed_2695_; lean_object* v_res_2696_; 
v_i_boxed_2694_ = lean_unbox_usize(v_i_2691_);
lean_dec(v_i_2691_);
v_stop_boxed_2695_ = lean_unbox_usize(v_stop_2692_);
lean_dec(v_stop_2692_);
v_res_2696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_as_2690_, v_i_boxed_2694_, v_stop_boxed_2695_, v_b_2693_);
lean_dec_ref(v_as_2690_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(lean_object* v_x_2697_, lean_object* v_x_2698_){
_start:
{
if (lean_obj_tag(v_x_2697_) == 0)
{
lean_object* v_cs_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_cs_2699_ = lean_ctor_get(v_x_2697_, 0);
v___x_2700_ = lean_unsigned_to_nat(0u);
v___x_2701_ = lean_array_get_size(v_cs_2699_);
v___x_2702_ = lean_nat_dec_lt(v___x_2700_, v___x_2701_);
if (v___x_2702_ == 0)
{
return v_x_2698_;
}
else
{
uint8_t v___x_2703_; 
v___x_2703_ = lean_nat_dec_le(v___x_2701_, v___x_2701_);
if (v___x_2703_ == 0)
{
if (v___x_2702_ == 0)
{
return v_x_2698_;
}
else
{
size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = lean_usize_of_nat(v___x_2701_);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31(v_cs_2699_, v___x_2704_, v___x_2705_, v_x_2698_);
return v___x_2706_;
}
}
else
{
size_t v___x_2707_; size_t v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = ((size_t)0ULL);
v___x_2708_ = lean_usize_of_nat(v___x_2701_);
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31(v_cs_2699_, v___x_2707_, v___x_2708_, v_x_2698_);
return v___x_2709_;
}
}
}
else
{
lean_object* v_vs_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_vs_2710_ = lean_ctor_get(v_x_2697_, 0);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_array_get_size(v_vs_2710_);
v___x_2713_ = lean_nat_dec_lt(v___x_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
return v_x_2698_;
}
else
{
uint8_t v___x_2714_; 
v___x_2714_ = lean_nat_dec_le(v___x_2712_, v___x_2712_);
if (v___x_2714_ == 0)
{
if (v___x_2713_ == 0)
{
return v_x_2698_;
}
else
{
size_t v___x_2715_; size_t v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = ((size_t)0ULL);
v___x_2716_ = lean_usize_of_nat(v___x_2712_);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2710_, v___x_2715_, v___x_2716_, v_x_2698_);
return v___x_2717_;
}
}
else
{
size_t v___x_2718_; size_t v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = ((size_t)0ULL);
v___x_2719_ = lean_usize_of_nat(v___x_2712_);
v___x_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2710_, v___x_2718_, v___x_2719_, v_x_2698_);
return v___x_2720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31(lean_object* v_as_2721_, size_t v_i_2722_, size_t v_stop_2723_, lean_object* v_b_2724_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_usize_dec_eq(v_i_2722_, v_stop_2723_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; size_t v___x_2728_; size_t v___x_2729_; 
v___x_2726_ = lean_array_uget_borrowed(v_as_2721_, v_i_2722_);
v___x_2727_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v___x_2726_, v_b_2724_);
v___x_2728_ = ((size_t)1ULL);
v___x_2729_ = lean_usize_add(v_i_2722_, v___x_2728_);
v_i_2722_ = v___x_2729_;
v_b_2724_ = v___x_2727_;
goto _start;
}
else
{
return v_b_2724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31___boxed(lean_object* v_as_2731_, lean_object* v_i_2732_, lean_object* v_stop_2733_, lean_object* v_b_2734_){
_start:
{
size_t v_i_boxed_2735_; size_t v_stop_boxed_2736_; lean_object* v_res_2737_; 
v_i_boxed_2735_ = lean_unbox_usize(v_i_2732_);
lean_dec(v_i_2732_);
v_stop_boxed_2736_ = lean_unbox_usize(v_stop_2733_);
lean_dec(v_stop_2733_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31(v_as_2731_, v_i_boxed_2735_, v_stop_boxed_2736_, v_b_2734_);
lean_dec_ref(v_as_2731_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(lean_object* v_x_2738_, lean_object* v_x_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_x_2738_, v_x_2739_);
lean_dec_ref(v_x_2738_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(lean_object* v_x_2741_, size_t v_x_2742_, size_t v_x_2743_, lean_object* v_x_2744_){
_start:
{
if (lean_obj_tag(v_x_2741_) == 0)
{
lean_object* v_cs_2745_; lean_object* v___x_2746_; size_t v___x_2747_; lean_object* v_j_2748_; lean_object* v___x_2749_; size_t v___x_2750_; size_t v___x_2751_; size_t v___x_2752_; size_t v___x_2753_; size_t v___x_2754_; size_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_cs_2745_ = lean_ctor_get(v_x_2741_, 0);
v___x_2746_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_2747_ = lean_usize_shift_right(v_x_2742_, v_x_2743_);
v_j_2748_ = lean_usize_to_nat(v___x_2747_);
v___x_2749_ = lean_array_get_borrowed(v___x_2746_, v_cs_2745_, v_j_2748_);
v___x_2750_ = ((size_t)1ULL);
v___x_2751_ = lean_usize_shift_left(v___x_2750_, v_x_2743_);
v___x_2752_ = lean_usize_sub(v___x_2751_, v___x_2750_);
v___x_2753_ = lean_usize_land(v_x_2742_, v___x_2752_);
v___x_2754_ = ((size_t)5ULL);
v___x_2755_ = lean_usize_sub(v_x_2743_, v___x_2754_);
v___x_2756_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v___x_2749_, v___x_2753_, v___x_2755_, v_x_2744_);
v___x_2757_ = lean_unsigned_to_nat(1u);
v___x_2758_ = lean_nat_add(v_j_2748_, v___x_2757_);
lean_dec(v_j_2748_);
v___x_2759_ = lean_array_get_size(v_cs_2745_);
v___x_2760_ = lean_nat_dec_lt(v___x_2758_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_dec(v___x_2758_);
return v___x_2756_;
}
else
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_nat_dec_le(v___x_2759_, v___x_2759_);
if (v___x_2761_ == 0)
{
if (v___x_2760_ == 0)
{
lean_dec(v___x_2758_);
return v___x_2756_;
}
else
{
size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = lean_usize_of_nat(v___x_2758_);
lean_dec(v___x_2758_);
v___x_2763_ = lean_usize_of_nat(v___x_2759_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31(v_cs_2745_, v___x_2762_, v___x_2763_, v___x_2756_);
return v___x_2764_;
}
}
else
{
size_t v___x_2765_; size_t v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = lean_usize_of_nat(v___x_2758_);
lean_dec(v___x_2758_);
v___x_2766_ = lean_usize_of_nat(v___x_2759_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__31(v_cs_2745_, v___x_2765_, v___x_2766_, v___x_2756_);
return v___x_2767_;
}
}
}
else
{
lean_object* v_vs_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_vs_2768_ = lean_ctor_get(v_x_2741_, 0);
v___x_2769_ = lean_usize_to_nat(v_x_2742_);
v___x_2770_ = lean_array_get_size(v_vs_2768_);
v___x_2771_ = lean_nat_dec_lt(v___x_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_dec(v___x_2769_);
return v_x_2744_;
}
else
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_nat_dec_le(v___x_2770_, v___x_2770_);
if (v___x_2772_ == 0)
{
if (v___x_2771_ == 0)
{
lean_dec(v___x_2769_);
return v_x_2744_;
}
else
{
size_t v___x_2773_; size_t v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = lean_usize_of_nat(v___x_2769_);
lean_dec(v___x_2769_);
v___x_2774_ = lean_usize_of_nat(v___x_2770_);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2768_, v___x_2773_, v___x_2774_, v_x_2744_);
return v___x_2775_;
}
}
else
{
size_t v___x_2776_; size_t v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = lean_usize_of_nat(v___x_2769_);
lean_dec(v___x_2769_);
v___x_2777_ = lean_usize_of_nat(v___x_2770_);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2768_, v___x_2776_, v___x_2777_, v_x_2744_);
return v___x_2778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(lean_object* v_x_2779_, lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_){
_start:
{
size_t v_x_86703__boxed_2783_; size_t v_x_86704__boxed_2784_; lean_object* v_res_2785_; 
v_x_86703__boxed_2783_ = lean_unbox_usize(v_x_2780_);
lean_dec(v_x_2780_);
v_x_86704__boxed_2784_ = lean_unbox_usize(v_x_2781_);
lean_dec(v_x_2781_);
v_res_2785_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_x_2779_, v_x_86703__boxed_2783_, v_x_86704__boxed_2784_, v_x_2782_);
lean_dec_ref(v_x_2779_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object* v_t_2786_, lean_object* v_init_2787_, lean_object* v_start_2788_){
_start:
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = lean_unsigned_to_nat(0u);
v___x_2790_ = lean_nat_dec_eq(v_start_2788_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v_root_2791_; lean_object* v_tail_2792_; size_t v_shift_2793_; lean_object* v_tailOff_2794_; uint8_t v___x_2795_; 
v_root_2791_ = lean_ctor_get(v_t_2786_, 0);
v_tail_2792_ = lean_ctor_get(v_t_2786_, 1);
v_shift_2793_ = lean_ctor_get_usize(v_t_2786_, 4);
v_tailOff_2794_ = lean_ctor_get(v_t_2786_, 3);
v___x_2795_ = lean_nat_dec_le(v_tailOff_2794_, v_start_2788_);
if (v___x_2795_ == 0)
{
size_t v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2796_ = lean_usize_of_nat(v_start_2788_);
v___x_2797_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_root_2791_, v___x_2796_, v_shift_2793_, v_init_2787_);
v___x_2798_ = lean_array_get_size(v_tail_2792_);
v___x_2799_ = lean_nat_dec_lt(v___x_2789_, v___x_2798_);
if (v___x_2799_ == 0)
{
return v___x_2797_;
}
else
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_nat_dec_le(v___x_2798_, v___x_2798_);
if (v___x_2800_ == 0)
{
if (v___x_2799_ == 0)
{
return v___x_2797_;
}
else
{
size_t v___x_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = ((size_t)0ULL);
v___x_2802_ = lean_usize_of_nat(v___x_2798_);
v___x_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2792_, v___x_2801_, v___x_2802_, v___x_2797_);
return v___x_2803_;
}
}
else
{
size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = lean_usize_of_nat(v___x_2798_);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2792_, v___x_2804_, v___x_2805_, v___x_2797_);
return v___x_2806_;
}
}
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2807_ = lean_nat_sub(v_start_2788_, v_tailOff_2794_);
v___x_2808_ = lean_array_get_size(v_tail_2792_);
v___x_2809_ = lean_nat_dec_lt(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_dec(v___x_2807_);
return v_init_2787_;
}
else
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_nat_dec_le(v___x_2808_, v___x_2808_);
if (v___x_2810_ == 0)
{
if (v___x_2809_ == 0)
{
lean_dec(v___x_2807_);
return v_init_2787_;
}
else
{
size_t v___x_2811_; size_t v___x_2812_; lean_object* v___x_2813_; 
v___x_2811_ = lean_usize_of_nat(v___x_2807_);
lean_dec(v___x_2807_);
v___x_2812_ = lean_usize_of_nat(v___x_2808_);
v___x_2813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2792_, v___x_2811_, v___x_2812_, v_init_2787_);
return v___x_2813_;
}
}
else
{
size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = lean_usize_of_nat(v___x_2807_);
lean_dec(v___x_2807_);
v___x_2815_ = lean_usize_of_nat(v___x_2808_);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2792_, v___x_2814_, v___x_2815_, v_init_2787_);
return v___x_2816_;
}
}
}
}
else
{
lean_object* v_root_2817_; lean_object* v_tail_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_root_2817_ = lean_ctor_get(v_t_2786_, 0);
v_tail_2818_ = lean_ctor_get(v_t_2786_, 1);
v___x_2819_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_root_2817_, v_init_2787_);
v___x_2820_ = lean_array_get_size(v_tail_2818_);
v___x_2821_ = lean_nat_dec_lt(v___x_2789_, v___x_2820_);
if (v___x_2821_ == 0)
{
return v___x_2819_;
}
else
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_nat_dec_le(v___x_2820_, v___x_2820_);
if (v___x_2822_ == 0)
{
if (v___x_2821_ == 0)
{
return v___x_2819_;
}
else
{
size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = lean_usize_of_nat(v___x_2820_);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2818_, v___x_2823_, v___x_2824_, v___x_2819_);
return v___x_2825_;
}
}
else
{
size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = lean_usize_of_nat(v___x_2820_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2818_, v___x_2826_, v___x_2827_, v___x_2819_);
return v___x_2828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object* v_t_2829_, lean_object* v_init_2830_, lean_object* v_start_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_t_2829_, v_init_2830_, v_start_2831_);
lean_dec(v_start_2831_);
lean_dec_ref(v_t_2829_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object* v___x_2833_, size_t v_sz_2834_, size_t v_i_2835_, lean_object* v_bs_2836_){
_start:
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_usize_dec_lt(v_i_2835_, v_sz_2834_);
if (v___x_2837_ == 0)
{
return v_bs_2836_;
}
else
{
lean_object* v_v_2838_; lean_object* v___x_2839_; lean_object* v_bs_x27_2840_; lean_object* v___x_2841_; size_t v___x_2842_; size_t v___x_2843_; lean_object* v___x_2844_; 
v_v_2838_ = lean_array_uget(v_bs_2836_, v_i_2835_);
v___x_2839_ = lean_unsigned_to_nat(0u);
v_bs_x27_2840_ = lean_array_uset(v_bs_2836_, v_i_2835_, v___x_2839_);
v___x_2841_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_v_2838_, v___x_2833_);
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_add(v_i_2835_, v___x_2842_);
v___x_2844_ = lean_array_uset(v_bs_x27_2840_, v_i_2835_, v___x_2841_);
v_i_2835_ = v___x_2843_;
v_bs_2836_ = v___x_2844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object* v___x_2846_, lean_object* v_sz_2847_, lean_object* v_i_2848_, lean_object* v_bs_2849_){
_start:
{
size_t v_sz_boxed_2850_; size_t v_i_boxed_2851_; lean_object* v_res_2852_; 
v_sz_boxed_2850_ = lean_unbox_usize(v_sz_2847_);
lean_dec(v_sz_2847_);
v_i_boxed_2851_ = lean_unbox_usize(v_i_2848_);
lean_dec(v_i_2848_);
v_res_2852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_2846_, v_sz_boxed_2850_, v_i_boxed_2851_, v_bs_2849_);
lean_dec_ref(v___x_2846_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object* v___x_2853_, size_t v_sz_2854_, size_t v_i_2855_, lean_object* v_bs_2856_){
_start:
{
uint8_t v___x_2857_; 
v___x_2857_ = lean_usize_dec_lt(v_i_2855_, v_sz_2854_);
if (v___x_2857_ == 0)
{
return v_bs_2856_;
}
else
{
lean_object* v_v_2858_; lean_object* v___x_2859_; lean_object* v_bs_x27_2860_; lean_object* v___x_2861_; size_t v___x_2862_; size_t v___x_2863_; lean_object* v___x_2864_; 
v_v_2858_ = lean_array_uget(v_bs_2856_, v_i_2855_);
v___x_2859_ = lean_unsigned_to_nat(0u);
v_bs_x27_2860_ = lean_array_uset(v_bs_2856_, v_i_2855_, v___x_2859_);
v___x_2861_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_v_2858_, v___x_2853_);
v___x_2862_ = ((size_t)1ULL);
v___x_2863_ = lean_usize_add(v_i_2855_, v___x_2862_);
v___x_2864_ = lean_array_uset(v_bs_x27_2860_, v_i_2855_, v___x_2861_);
v_i_2855_ = v___x_2863_;
v_bs_2856_ = v___x_2864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object* v___x_2866_, lean_object* v_sz_2867_, lean_object* v_i_2868_, lean_object* v_bs_2869_){
_start:
{
size_t v_sz_boxed_2870_; size_t v_i_boxed_2871_; lean_object* v_res_2872_; 
v_sz_boxed_2870_ = lean_unbox_usize(v_sz_2867_);
lean_dec(v_sz_2867_);
v_i_boxed_2871_ = lean_unbox_usize(v_i_2868_);
lean_dec(v_i_2868_);
v_res_2872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_2866_, v_sz_boxed_2870_, v_i_boxed_2871_, v_bs_2869_);
lean_dec_ref(v___x_2866_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
if (lean_obj_tag(v_a_2873_) == 0)
{
lean_object* v___x_2875_; 
v___x_2875_ = l_List_reverse___redArg(v_a_2874_);
return v___x_2875_;
}
else
{
lean_object* v_head_2876_; lean_object* v_tail_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2888_; 
v_head_2876_ = lean_ctor_get(v_a_2873_, 0);
v_tail_2877_ = lean_ctor_get(v_a_2873_, 1);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_a_2873_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2879_ = v_a_2873_;
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_tail_2877_);
lean_inc(v_head_2876_);
lean_dec(v_a_2873_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2881_ = l_Nat_reprFast(v_head_2876_);
v___x_2882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
v___x_2883_ = l_Lean_MessageData_ofFormat(v___x_2882_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 1, v_a_2874_);
lean_ctor_set(v___x_2879_, 0, v___x_2883_);
v___x_2885_ = v___x_2879_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_a_2874_);
v___x_2885_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
v_a_2873_ = v_tail_2877_;
v_a_2874_ = v___x_2885_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object* v___x_2889_, size_t v_sz_2890_, size_t v_i_2891_, lean_object* v_bs_2892_){
_start:
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_usize_dec_lt(v_i_2891_, v_sz_2890_);
if (v___x_2893_ == 0)
{
return v_bs_2892_;
}
else
{
lean_object* v_v_2894_; lean_object* v___x_2895_; lean_object* v_bs_x27_2896_; lean_object* v___x_2897_; size_t v___x_2898_; size_t v___x_2899_; lean_object* v___x_2900_; 
v_v_2894_ = lean_array_uget(v_bs_2892_, v_i_2891_);
v___x_2895_ = lean_unsigned_to_nat(0u);
v_bs_x27_2896_ = lean_array_uset(v_bs_2892_, v_i_2891_, v___x_2895_);
v___x_2897_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_2894_, v___x_2889_);
v___x_2898_ = ((size_t)1ULL);
v___x_2899_ = lean_usize_add(v_i_2891_, v___x_2898_);
v___x_2900_ = lean_array_uset(v_bs_x27_2896_, v_i_2891_, v___x_2897_);
v_i_2891_ = v___x_2899_;
v_bs_2892_ = v___x_2900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object* v___x_2902_, lean_object* v_sz_2903_, lean_object* v_i_2904_, lean_object* v_bs_2905_){
_start:
{
size_t v_sz_boxed_2906_; size_t v_i_boxed_2907_; lean_object* v_res_2908_; 
v_sz_boxed_2906_ = lean_unbox_usize(v_sz_2903_);
lean_dec(v_sz_2903_);
v_i_boxed_2907_ = lean_unbox_usize(v_i_2904_);
lean_dec(v_i_2904_);
v_res_2908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_2902_, v_sz_boxed_2906_, v_i_boxed_2907_, v_bs_2905_);
lean_dec_ref(v___x_2902_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object* v_as_2909_, size_t v_sz_2910_, size_t v_i_2911_, lean_object* v_b_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
uint8_t v___x_2924_; 
v___x_2924_ = lean_usize_dec_lt(v_i_2911_, v_sz_2910_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_b_2912_);
return v___x_2925_;
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2927_; 
v_a_2926_ = lean_array_uget_borrowed(v_as_2909_, v_i_2911_);
lean_inc(v_a_2926_);
v___x_2927_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(v_a_2926_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; 
lean_dec_ref(v___x_2927_);
v___x_2928_ = lean_box(0);
v___x_2929_ = ((size_t)1ULL);
v___x_2930_ = lean_usize_add(v_i_2911_, v___x_2929_);
v_i_2911_ = v___x_2930_;
v_b_2912_ = v___x_2928_;
goto _start;
}
else
{
return v___x_2927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object* v_as_2932_, lean_object* v_sz_2933_, lean_object* v_i_2934_, lean_object* v_b_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
size_t v_sz_boxed_2947_; size_t v_i_boxed_2948_; lean_object* v_res_2949_; 
v_sz_boxed_2947_ = lean_unbox_usize(v_sz_2933_);
lean_dec(v_sz_2933_);
v_i_boxed_2948_ = lean_unbox_usize(v_i_2934_);
lean_dec(v_i_2934_);
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_2932_, v_sz_boxed_2947_, v_i_boxed_2948_, v_b_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v_as_2932_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object* v_as_2950_, size_t v_sz_2951_, size_t v_i_2952_, lean_object* v_b_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
uint8_t v___x_2965_; 
v___x_2965_ = lean_usize_dec_lt(v_i_2952_, v_sz_2951_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v_b_2953_);
return v___x_2966_;
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2968_; 
v_a_2967_ = lean_array_uget_borrowed(v_as_2950_, v_i_2952_);
lean_inc(v___y_2963_);
lean_inc_ref(v___y_2962_);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
lean_inc(v___y_2957_);
lean_inc_ref(v___y_2956_);
lean_inc(v___y_2955_);
lean_inc(v___y_2954_);
lean_inc(v_a_2967_);
v___x_2968_ = lean_grind_cutsat_assert_le(v_a_2967_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; 
lean_dec_ref(v___x_2968_);
v___x_2969_ = lean_box(0);
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_add(v_i_2952_, v___x_2970_);
v_i_2952_ = v___x_2971_;
v_b_2953_ = v___x_2969_;
goto _start;
}
else
{
return v___x_2968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object* v_as_2973_, lean_object* v_sz_2974_, lean_object* v_i_2975_, lean_object* v_b_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
size_t v_sz_boxed_2988_; size_t v_i_boxed_2989_; lean_object* v_res_2990_; 
v_sz_boxed_2988_ = lean_unbox_usize(v_sz_2974_);
lean_dec(v_sz_2974_);
v_i_boxed_2989_ = lean_unbox_usize(v_i_2975_);
lean_dec(v_i_2975_);
v_res_2990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v_as_2973_, v_sz_boxed_2988_, v_i_boxed_2989_, v_b_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(lean_object* v_msgData_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; lean_object* v_env_2998_; lean_object* v___x_2999_; lean_object* v_mctx_3000_; lean_object* v_lctx_3001_; lean_object* v_options_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_2997_ = lean_st_ref_get(v___y_2995_);
v_env_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc_ref(v_env_2998_);
lean_dec(v___x_2997_);
v___x_2999_ = lean_st_ref_get(v___y_2993_);
v_mctx_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_mctx_3000_);
lean_dec(v___x_2999_);
v_lctx_3001_ = lean_ctor_get(v___y_2992_, 2);
v_options_3002_ = lean_ctor_get(v___y_2994_, 2);
lean_inc_ref(v_options_3002_);
lean_inc_ref(v_lctx_3001_);
v___x_3003_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3003_, 0, v_env_2998_);
lean_ctor_set(v___x_3003_, 1, v_mctx_3000_);
lean_ctor_set(v___x_3003_, 2, v_lctx_3001_);
lean_ctor_set(v___x_3003_, 3, v_options_3002_);
v___x_3004_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
lean_ctor_set(v___x_3004_, 1, v_msgData_2991_);
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38___boxed(lean_object* v_msgData_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msgData_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
return v_res_3012_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_3013_; double v___x_3014_; 
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_float_of_nat(v___x_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(lean_object* v_cls_3018_, lean_object* v_msg_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_ref_3025_; lean_object* v___x_3026_; lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3071_; 
v_ref_3025_ = lean_ctor_get(v___y_3022_, 5);
v___x_3026_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msg_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3071_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3071_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v_traceState_3032_; lean_object* v_env_3033_; lean_object* v_nextMacroScope_3034_; lean_object* v_ngen_3035_; lean_object* v_auxDeclNGen_3036_; lean_object* v_cache_3037_; lean_object* v_messages_3038_; lean_object* v_infoState_3039_; lean_object* v_snapshotTasks_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3070_; 
v___x_3031_ = lean_st_ref_take(v___y_3023_);
v_traceState_3032_ = lean_ctor_get(v___x_3031_, 4);
v_env_3033_ = lean_ctor_get(v___x_3031_, 0);
v_nextMacroScope_3034_ = lean_ctor_get(v___x_3031_, 1);
v_ngen_3035_ = lean_ctor_get(v___x_3031_, 2);
v_auxDeclNGen_3036_ = lean_ctor_get(v___x_3031_, 3);
v_cache_3037_ = lean_ctor_get(v___x_3031_, 5);
v_messages_3038_ = lean_ctor_get(v___x_3031_, 6);
v_infoState_3039_ = lean_ctor_get(v___x_3031_, 7);
v_snapshotTasks_3040_ = lean_ctor_get(v___x_3031_, 8);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3042_ = v___x_3031_;
v_isShared_3043_ = v_isSharedCheck_3070_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_snapshotTasks_3040_);
lean_inc(v_infoState_3039_);
lean_inc(v_messages_3038_);
lean_inc(v_cache_3037_);
lean_inc(v_traceState_3032_);
lean_inc(v_auxDeclNGen_3036_);
lean_inc(v_ngen_3035_);
lean_inc(v_nextMacroScope_3034_);
lean_inc(v_env_3033_);
lean_dec(v___x_3031_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3070_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
uint64_t v_tid_3044_; lean_object* v_traces_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3069_; 
v_tid_3044_ = lean_ctor_get_uint64(v_traceState_3032_, sizeof(void*)*1);
v_traces_3045_ = lean_ctor_get(v_traceState_3032_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_traceState_3032_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3047_ = v_traceState_3032_;
v_isShared_3048_ = v_isSharedCheck_3069_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_traces_3045_);
lean_dec(v_traceState_3032_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3069_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; double v___x_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3049_ = lean_box(0);
v___x_3050_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0);
v___x_3051_ = 0;
v___x_3052_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1));
v___x_3053_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3053_, 0, v_cls_3018_);
lean_ctor_set(v___x_3053_, 1, v___x_3049_);
lean_ctor_set(v___x_3053_, 2, v___x_3052_);
lean_ctor_set_float(v___x_3053_, sizeof(void*)*3, v___x_3050_);
lean_ctor_set_float(v___x_3053_, sizeof(void*)*3 + 8, v___x_3050_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*3 + 16, v___x_3051_);
v___x_3054_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2));
v___x_3055_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3053_);
lean_ctor_set(v___x_3055_, 1, v_a_3027_);
lean_ctor_set(v___x_3055_, 2, v___x_3054_);
lean_inc(v_ref_3025_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v_ref_3025_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = l_Lean_PersistentArray_push___redArg(v_traces_3045_, v___x_3056_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3057_);
v___x_3059_ = v___x_3047_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3057_);
lean_ctor_set_uint64(v_reuseFailAlloc_3068_, sizeof(void*)*1, v_tid_3044_);
v___x_3059_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3061_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 4, v___x_3059_);
v___x_3061_ = v___x_3042_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_env_3033_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_nextMacroScope_3034_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_ngen_3035_);
lean_ctor_set(v_reuseFailAlloc_3067_, 3, v_auxDeclNGen_3036_);
lean_ctor_set(v_reuseFailAlloc_3067_, 4, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3067_, 5, v_cache_3037_);
lean_ctor_set(v_reuseFailAlloc_3067_, 6, v_messages_3038_);
lean_ctor_set(v_reuseFailAlloc_3067_, 7, v_infoState_3039_);
lean_ctor_set(v_reuseFailAlloc_3067_, 8, v_snapshotTasks_3040_);
v___x_3061_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3062_ = lean_st_ref_set(v___y_3023_, v___x_3061_);
v___x_3063_ = lean_box(0);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3063_);
v___x_3065_ = v___x_3029_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___boxed(lean_object* v_cls_3072_, lean_object* v_msg_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3072_, v_msg_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object* v_as_3080_, size_t v_sz_3081_, size_t v_i_3082_, lean_object* v_b_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
uint8_t v___x_3095_; 
v___x_3095_ = lean_usize_dec_lt(v_i_3082_, v_sz_3081_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v_b_3083_);
return v___x_3096_;
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3098_; 
v_a_3097_ = lean_array_uget_borrowed(v_as_3080_, v_i_3082_);
lean_inc_ref(v___y_3092_);
lean_inc(v_a_3097_);
v___x_3098_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_a_3097_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v___x_3099_; size_t v___x_3100_; size_t v___x_3101_; 
lean_dec_ref(v___x_3098_);
v___x_3099_ = lean_box(0);
v___x_3100_ = ((size_t)1ULL);
v___x_3101_ = lean_usize_add(v_i_3082_, v___x_3100_);
v_i_3082_ = v___x_3101_;
v_b_3083_ = v___x_3099_;
goto _start;
}
else
{
return v___x_3098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object* v_as_3103_, lean_object* v_sz_3104_, lean_object* v_i_3105_, lean_object* v_b_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
size_t v_sz_boxed_3118_; size_t v_i_boxed_3119_; lean_object* v_res_3120_; 
v_sz_boxed_3118_ = lean_unbox_usize(v_sz_3104_);
lean_dec(v_sz_3104_);
v_i_boxed_3119_ = lean_unbox_usize(v_i_3105_);
lean_dec(v_i_3105_);
v_res_3120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v_as_3103_, v_sz_boxed_3118_, v_i_boxed_3119_, v_b_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v_as_3103_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(lean_object* v_as_3121_, size_t v_i_3122_, size_t v_stop_3123_, lean_object* v_b_3124_){
_start:
{
uint8_t v___x_3125_; 
v___x_3125_ = lean_usize_dec_eq(v_i_3122_, v_stop_3123_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; size_t v___x_3129_; size_t v___x_3130_; 
v___x_3126_ = lean_array_uget_borrowed(v_as_3121_, v_i_3122_);
v___x_3127_ = l_Lean_PersistentArray_toArray___redArg(v___x_3126_);
v___x_3128_ = l_Array_append___redArg(v_b_3124_, v___x_3127_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = ((size_t)1ULL);
v___x_3130_ = lean_usize_add(v_i_3122_, v___x_3129_);
v_i_3122_ = v___x_3130_;
v_b_3124_ = v___x_3128_;
goto _start;
}
else
{
return v_b_3124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(lean_object* v_as_3132_, lean_object* v_i_3133_, lean_object* v_stop_3134_, lean_object* v_b_3135_){
_start:
{
size_t v_i_boxed_3136_; size_t v_stop_boxed_3137_; lean_object* v_res_3138_; 
v_i_boxed_3136_ = lean_unbox_usize(v_i_3133_);
lean_dec(v_i_3133_);
v_stop_boxed_3137_ = lean_unbox_usize(v_stop_3134_);
lean_dec(v_stop_3134_);
v_res_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_as_3132_, v_i_boxed_3136_, v_stop_boxed_3137_, v_b_3135_);
lean_dec_ref(v_as_3132_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(lean_object* v_x_3139_, lean_object* v_x_3140_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 0)
{
lean_object* v_cs_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v_cs_3141_ = lean_ctor_get(v_x_3139_, 0);
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_array_get_size(v_cs_3141_);
v___x_3144_ = lean_nat_dec_lt(v___x_3142_, v___x_3143_);
if (v___x_3144_ == 0)
{
return v_x_3140_;
}
else
{
uint8_t v___x_3145_; 
v___x_3145_ = lean_nat_dec_le(v___x_3143_, v___x_3143_);
if (v___x_3145_ == 0)
{
if (v___x_3144_ == 0)
{
return v_x_3140_;
}
else
{
size_t v___x_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = ((size_t)0ULL);
v___x_3147_ = lean_usize_of_nat(v___x_3143_);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36(v_cs_3141_, v___x_3146_, v___x_3147_, v_x_3140_);
return v___x_3148_;
}
}
else
{
size_t v___x_3149_; size_t v___x_3150_; lean_object* v___x_3151_; 
v___x_3149_ = ((size_t)0ULL);
v___x_3150_ = lean_usize_of_nat(v___x_3143_);
v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36(v_cs_3141_, v___x_3149_, v___x_3150_, v_x_3140_);
return v___x_3151_;
}
}
}
else
{
lean_object* v_vs_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v_vs_3152_ = lean_ctor_get(v_x_3139_, 0);
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = lean_array_get_size(v_vs_3152_);
v___x_3155_ = lean_nat_dec_lt(v___x_3153_, v___x_3154_);
if (v___x_3155_ == 0)
{
return v_x_3140_;
}
else
{
uint8_t v___x_3156_; 
v___x_3156_ = lean_nat_dec_le(v___x_3154_, v___x_3154_);
if (v___x_3156_ == 0)
{
if (v___x_3155_ == 0)
{
return v_x_3140_;
}
else
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = ((size_t)0ULL);
v___x_3158_ = lean_usize_of_nat(v___x_3154_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3152_, v___x_3157_, v___x_3158_, v_x_3140_);
return v___x_3159_;
}
}
else
{
size_t v___x_3160_; size_t v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = ((size_t)0ULL);
v___x_3161_ = lean_usize_of_nat(v___x_3154_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3152_, v___x_3160_, v___x_3161_, v_x_3140_);
return v___x_3162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36(lean_object* v_as_3163_, size_t v_i_3164_, size_t v_stop_3165_, lean_object* v_b_3166_){
_start:
{
uint8_t v___x_3167_; 
v___x_3167_ = lean_usize_dec_eq(v_i_3164_, v_stop_3165_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; lean_object* v___x_3169_; size_t v___x_3170_; size_t v___x_3171_; 
v___x_3168_ = lean_array_uget_borrowed(v_as_3163_, v_i_3164_);
v___x_3169_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v___x_3168_, v_b_3166_);
v___x_3170_ = ((size_t)1ULL);
v___x_3171_ = lean_usize_add(v_i_3164_, v___x_3170_);
v_i_3164_ = v___x_3171_;
v_b_3166_ = v___x_3169_;
goto _start;
}
else
{
return v_b_3166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36___boxed(lean_object* v_as_3173_, lean_object* v_i_3174_, lean_object* v_stop_3175_, lean_object* v_b_3176_){
_start:
{
size_t v_i_boxed_3177_; size_t v_stop_boxed_3178_; lean_object* v_res_3179_; 
v_i_boxed_3177_ = lean_unbox_usize(v_i_3174_);
lean_dec(v_i_3174_);
v_stop_boxed_3178_ = lean_unbox_usize(v_stop_3175_);
lean_dec(v_stop_3175_);
v_res_3179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36(v_as_3173_, v_i_boxed_3177_, v_stop_boxed_3178_, v_b_3176_);
lean_dec_ref(v_as_3173_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28___boxed(lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_x_3180_, v_x_3181_);
lean_dec_ref(v_x_3180_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(lean_object* v_x_3183_, size_t v_x_3184_, size_t v_x_3185_, lean_object* v_x_3186_){
_start:
{
if (lean_obj_tag(v_x_3183_) == 0)
{
lean_object* v_cs_3187_; lean_object* v___x_3188_; size_t v___x_3189_; lean_object* v_j_3190_; lean_object* v___x_3191_; size_t v___x_3192_; size_t v___x_3193_; size_t v___x_3194_; size_t v___x_3195_; size_t v___x_3196_; size_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_cs_3187_ = lean_ctor_get(v_x_3183_, 0);
v___x_3188_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_3189_ = lean_usize_shift_right(v_x_3184_, v_x_3185_);
v_j_3190_ = lean_usize_to_nat(v___x_3189_);
v___x_3191_ = lean_array_get_borrowed(v___x_3188_, v_cs_3187_, v_j_3190_);
v___x_3192_ = ((size_t)1ULL);
v___x_3193_ = lean_usize_shift_left(v___x_3192_, v_x_3185_);
v___x_3194_ = lean_usize_sub(v___x_3193_, v___x_3192_);
v___x_3195_ = lean_usize_land(v_x_3184_, v___x_3194_);
v___x_3196_ = ((size_t)5ULL);
v___x_3197_ = lean_usize_sub(v_x_3185_, v___x_3196_);
v___x_3198_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v___x_3191_, v___x_3195_, v___x_3197_, v_x_3186_);
v___x_3199_ = lean_unsigned_to_nat(1u);
v___x_3200_ = lean_nat_add(v_j_3190_, v___x_3199_);
lean_dec(v_j_3190_);
v___x_3201_ = lean_array_get_size(v_cs_3187_);
v___x_3202_ = lean_nat_dec_lt(v___x_3200_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_dec(v___x_3200_);
return v___x_3198_;
}
else
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_nat_dec_le(v___x_3201_, v___x_3201_);
if (v___x_3203_ == 0)
{
if (v___x_3202_ == 0)
{
lean_dec(v___x_3200_);
return v___x_3198_;
}
else
{
size_t v___x_3204_; size_t v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_usize_of_nat(v___x_3200_);
lean_dec(v___x_3200_);
v___x_3205_ = lean_usize_of_nat(v___x_3201_);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36(v_cs_3187_, v___x_3204_, v___x_3205_, v___x_3198_);
return v___x_3206_;
}
}
else
{
size_t v___x_3207_; size_t v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_usize_of_nat(v___x_3200_);
lean_dec(v___x_3200_);
v___x_3208_ = lean_usize_of_nat(v___x_3201_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__36(v_cs_3187_, v___x_3207_, v___x_3208_, v___x_3198_);
return v___x_3209_;
}
}
}
else
{
lean_object* v_vs_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v_vs_3210_ = lean_ctor_get(v_x_3183_, 0);
v___x_3211_ = lean_usize_to_nat(v_x_3184_);
v___x_3212_ = lean_array_get_size(v_vs_3210_);
v___x_3213_ = lean_nat_dec_lt(v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_dec(v___x_3211_);
return v_x_3186_;
}
else
{
uint8_t v___x_3214_; 
v___x_3214_ = lean_nat_dec_le(v___x_3212_, v___x_3212_);
if (v___x_3214_ == 0)
{
if (v___x_3213_ == 0)
{
lean_dec(v___x_3211_);
return v_x_3186_;
}
else
{
size_t v___x_3215_; size_t v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = lean_usize_of_nat(v___x_3211_);
lean_dec(v___x_3211_);
v___x_3216_ = lean_usize_of_nat(v___x_3212_);
v___x_3217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3210_, v___x_3215_, v___x_3216_, v_x_3186_);
return v___x_3217_;
}
}
else
{
size_t v___x_3218_; size_t v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = lean_usize_of_nat(v___x_3211_);
lean_dec(v___x_3211_);
v___x_3219_ = lean_usize_of_nat(v___x_3212_);
v___x_3220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3210_, v___x_3218_, v___x_3219_, v_x_3186_);
return v___x_3220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26___boxed(lean_object* v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_, lean_object* v_x_3224_){
_start:
{
size_t v_x_87282__boxed_3225_; size_t v_x_87283__boxed_3226_; lean_object* v_res_3227_; 
v_x_87282__boxed_3225_ = lean_unbox_usize(v_x_3222_);
lean_dec(v_x_3222_);
v_x_87283__boxed_3226_ = lean_unbox_usize(v_x_3223_);
lean_dec(v_x_3223_);
v_res_3227_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_x_3221_, v_x_87282__boxed_3225_, v_x_87283__boxed_3226_, v_x_3224_);
lean_dec_ref(v_x_3221_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object* v_t_3228_, lean_object* v_init_3229_, lean_object* v_start_3230_){
_start:
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = lean_nat_dec_eq(v_start_3230_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v_root_3233_; lean_object* v_tail_3234_; size_t v_shift_3235_; lean_object* v_tailOff_3236_; uint8_t v___x_3237_; 
v_root_3233_ = lean_ctor_get(v_t_3228_, 0);
v_tail_3234_ = lean_ctor_get(v_t_3228_, 1);
v_shift_3235_ = lean_ctor_get_usize(v_t_3228_, 4);
v_tailOff_3236_ = lean_ctor_get(v_t_3228_, 3);
v___x_3237_ = lean_nat_dec_le(v_tailOff_3236_, v_start_3230_);
if (v___x_3237_ == 0)
{
size_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3238_ = lean_usize_of_nat(v_start_3230_);
v___x_3239_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_root_3233_, v___x_3238_, v_shift_3235_, v_init_3229_);
v___x_3240_ = lean_array_get_size(v_tail_3234_);
v___x_3241_ = lean_nat_dec_lt(v___x_3231_, v___x_3240_);
if (v___x_3241_ == 0)
{
return v___x_3239_;
}
else
{
uint8_t v___x_3242_; 
v___x_3242_ = lean_nat_dec_le(v___x_3240_, v___x_3240_);
if (v___x_3242_ == 0)
{
if (v___x_3241_ == 0)
{
return v___x_3239_;
}
else
{
size_t v___x_3243_; size_t v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = ((size_t)0ULL);
v___x_3244_ = lean_usize_of_nat(v___x_3240_);
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3234_, v___x_3243_, v___x_3244_, v___x_3239_);
return v___x_3245_;
}
}
else
{
size_t v___x_3246_; size_t v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = ((size_t)0ULL);
v___x_3247_ = lean_usize_of_nat(v___x_3240_);
v___x_3248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3234_, v___x_3246_, v___x_3247_, v___x_3239_);
return v___x_3248_;
}
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3249_ = lean_nat_sub(v_start_3230_, v_tailOff_3236_);
v___x_3250_ = lean_array_get_size(v_tail_3234_);
v___x_3251_ = lean_nat_dec_lt(v___x_3249_, v___x_3250_);
if (v___x_3251_ == 0)
{
lean_dec(v___x_3249_);
return v_init_3229_;
}
else
{
uint8_t v___x_3252_; 
v___x_3252_ = lean_nat_dec_le(v___x_3250_, v___x_3250_);
if (v___x_3252_ == 0)
{
if (v___x_3251_ == 0)
{
lean_dec(v___x_3249_);
return v_init_3229_;
}
else
{
size_t v___x_3253_; size_t v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_usize_of_nat(v___x_3249_);
lean_dec(v___x_3249_);
v___x_3254_ = lean_usize_of_nat(v___x_3250_);
v___x_3255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3234_, v___x_3253_, v___x_3254_, v_init_3229_);
return v___x_3255_;
}
}
else
{
size_t v___x_3256_; size_t v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = lean_usize_of_nat(v___x_3249_);
lean_dec(v___x_3249_);
v___x_3257_ = lean_usize_of_nat(v___x_3250_);
v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3234_, v___x_3256_, v___x_3257_, v_init_3229_);
return v___x_3258_;
}
}
}
}
else
{
lean_object* v_root_3259_; lean_object* v_tail_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v_root_3259_ = lean_ctor_get(v_t_3228_, 0);
v_tail_3260_ = lean_ctor_get(v_t_3228_, 1);
v___x_3261_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_root_3259_, v_init_3229_);
v___x_3262_ = lean_array_get_size(v_tail_3260_);
v___x_3263_ = lean_nat_dec_lt(v___x_3231_, v___x_3262_);
if (v___x_3263_ == 0)
{
return v___x_3261_;
}
else
{
uint8_t v___x_3264_; 
v___x_3264_ = lean_nat_dec_le(v___x_3262_, v___x_3262_);
if (v___x_3264_ == 0)
{
if (v___x_3263_ == 0)
{
return v___x_3261_;
}
else
{
size_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = ((size_t)0ULL);
v___x_3266_ = lean_usize_of_nat(v___x_3262_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3260_, v___x_3265_, v___x_3266_, v___x_3261_);
return v___x_3267_;
}
}
else
{
size_t v___x_3268_; size_t v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = ((size_t)0ULL);
v___x_3269_ = lean_usize_of_nat(v___x_3262_);
v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3260_, v___x_3268_, v___x_3269_, v___x_3261_);
return v___x_3270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object* v_t_3271_, lean_object* v_init_3272_, lean_object* v_start_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_t_3271_, v_init_3272_, v_start_3273_);
lean_dec(v_start_3273_);
lean_dec_ref(v_t_3271_);
return v_res_3274_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7));
v___x_3290_ = l_Lean_stringToMessageData(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9));
v___x_3293_ = l_Lean_stringToMessageData(v___x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3294_, v_a_3302_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3396_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3396_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3396_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_vars_3310_; lean_object* v_vars_x27_3311_; lean_object* v_dvds_3312_; lean_object* v_lowers_3313_; lean_object* v_uppers_3314_; lean_object* v_diseqs_3315_; uint8_t v___x_3316_; 
v_vars_3310_ = lean_ctor_get(v_a_3306_, 0);
lean_inc_ref(v_vars_3310_);
v_vars_x27_3311_ = lean_ctor_get(v_a_3306_, 2);
lean_inc_ref(v_vars_x27_3311_);
v_dvds_3312_ = lean_ctor_get(v_a_3306_, 6);
lean_inc_ref(v_dvds_3312_);
v_lowers_3313_ = lean_ctor_get(v_a_3306_, 7);
lean_inc_ref(v_lowers_3313_);
v_uppers_3314_ = lean_ctor_get(v_a_3306_, 8);
lean_inc_ref(v_uppers_3314_);
v_diseqs_3315_ = lean_ctor_get(v_a_3306_, 9);
lean_inc_ref(v_diseqs_3315_);
lean_dec(v_a_3306_);
v___x_3316_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_3310_);
lean_dec_ref(v_vars_3310_);
if (v___x_3316_ == 0)
{
uint8_t v___x_3317_; 
v___x_3317_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_x27_3311_);
lean_dec_ref(v_vars_x27_3311_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3320_; 
lean_dec_ref(v_diseqs_3315_);
lean_dec_ref(v_uppers_3314_);
lean_dec_ref(v_lowers_3313_);
lean_dec_ref(v_dvds_3312_);
v___x_3318_ = lean_box(0);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3318_);
v___x_3320_ = v___x_3308_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
else
{
lean_object* v___x_3322_; 
lean_del_object(v___x_3308_);
v___x_3322_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v___x_3323_; 
lean_dec_ref(v___x_3322_);
v___x_3323_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3325_; lean_object* v___f_3326_; lean_object* v___f_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref(v___x_3323_);
v___x_3325_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_3324_);
lean_inc_ref(v___x_3325_);
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3326_, 0, v___x_3325_);
lean_inc_ref(v___x_3325_);
lean_inc(v_a_3324_);
v___f_3327_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3327_, 0, v_a_3324_);
lean_closure_set(v___f_3327_, 1, v___f_3326_);
lean_closure_set(v___f_3327_, 2, v___x_3325_);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0));
v___x_3330_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_dvds_3312_, v___x_3329_, v___x_3328_);
lean_dec_ref(v_dvds_3312_);
v___x_3331_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_lowers_3313_, v___x_3329_, v___x_3328_);
lean_dec_ref(v_lowers_3313_);
v___x_3332_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3333_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3332_, v___f_3327_, v_a_3294_);
if (lean_obj_tag(v___x_3333_) == 0)
{
size_t v_sz_3334_; size_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; size_t v_sz_3338_; lean_object* v___x_3339_; 
lean_dec_ref(v___x_3333_);
v_sz_3334_ = lean_array_size(v___x_3330_);
v___x_3335_ = ((size_t)0ULL);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_3325_, v_sz_3334_, v___x_3335_, v___x_3330_);
v___x_3337_ = lean_box(0);
v_sz_3338_ = lean_array_size(v___x_3336_);
v___x_3339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_3336_, v_sz_3338_, v___x_3335_, v___x_3337_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
lean_dec_ref(v___x_3336_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3340_; size_t v_sz_3341_; lean_object* v___x_3342_; size_t v_sz_3343_; lean_object* v___x_3344_; 
lean_dec_ref(v___x_3339_);
v___x_3340_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_uppers_3314_, v___x_3331_, v___x_3328_);
lean_dec_ref(v_uppers_3314_);
v_sz_3341_ = lean_array_size(v___x_3340_);
v___x_3342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_3325_, v_sz_3341_, v___x_3335_, v___x_3340_);
v_sz_3343_ = lean_array_size(v___x_3342_);
v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_3342_, v_sz_3343_, v___x_3335_, v___x_3337_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
lean_dec_ref(v___x_3342_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; size_t v_sz_3346_; lean_object* v___x_3347_; size_t v_sz_3348_; lean_object* v___x_3349_; 
lean_dec_ref(v___x_3344_);
v___x_3345_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_diseqs_3315_, v___x_3329_, v___x_3328_);
lean_dec_ref(v_diseqs_3315_);
v_sz_3346_ = lean_array_size(v___x_3345_);
v___x_3347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_3325_, v_sz_3346_, v___x_3335_, v___x_3345_);
v_sz_3348_ = lean_array_size(v___x_3347_);
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_3347_, v_sz_3348_, v___x_3335_, v___x_3337_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
lean_dec_ref(v___x_3347_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v___x_3350_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___x_3374_; lean_object* v_a_3375_; uint8_t v___x_3376_; 
lean_dec_ref(v___x_3349_);
v___x_3350_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6));
v___x_3374_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg(v___x_3350_, v_a_3302_);
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref(v___x_3374_);
v___x_3376_ = lean_unbox(v_a_3375_);
lean_dec(v_a_3375_);
if (v___x_3376_ == 0)
{
lean_dec(v_a_3324_);
v___y_3352_ = v_a_3294_;
v___y_3353_ = v_a_3295_;
v___y_3354_ = v_a_3296_;
v___y_3355_ = v_a_3297_;
v___y_3356_ = v_a_3298_;
v___y_3357_ = v_a_3299_;
v___y_3358_ = v_a_3300_;
v___y_3359_ = v_a_3301_;
v___y_3360_ = v_a_3302_;
v___y_3361_ = v_a_3303_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3377_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10);
v___x_3378_ = lean_array_to_list(v_a_3324_);
v___x_3379_ = lean_box(0);
v___x_3380_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3378_, v___x_3379_);
v___x_3381_ = l_Lean_MessageData_ofList(v___x_3380_);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3377_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3350_, v___x_3382_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_dec_ref(v___x_3383_);
v___y_3352_ = v_a_3294_;
v___y_3353_ = v_a_3295_;
v___y_3354_ = v_a_3296_;
v___y_3355_ = v_a_3297_;
v___y_3356_ = v_a_3298_;
v___y_3357_ = v_a_3299_;
v___y_3358_ = v_a_3300_;
v___y_3359_ = v_a_3301_;
v___y_3360_ = v_a_3302_;
v___y_3361_ = v_a_3303_;
goto v___jp_3351_;
}
else
{
lean_dec_ref(v___x_3325_);
return v___x_3383_;
}
}
v___jp_3351_:
{
lean_object* v___x_3362_; lean_object* v_a_3363_; uint8_t v___x_3364_; 
v___x_3362_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___redArg(v___x_3350_, v___y_3360_);
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref(v___x_3362_);
v___x_3364_ = lean_unbox(v_a_3363_);
lean_dec(v_a_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_dec_ref(v___x_3325_);
v___x_3365_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3366_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8);
v___x_3367_ = lean_array_to_list(v___x_3325_);
v___x_3368_ = lean_box(0);
v___x_3369_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3367_, v___x_3368_);
v___x_3370_ = l_Lean_MessageData_ofList(v___x_3369_);
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3366_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3350_, v___x_3371_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v___x_3373_; 
lean_dec_ref(v___x_3372_);
v___x_3373_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
return v___x_3373_;
}
else
{
return v___x_3372_;
}
}
}
}
else
{
lean_dec_ref(v___x_3325_);
lean_dec(v_a_3324_);
return v___x_3349_;
}
}
else
{
lean_dec_ref(v___x_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_diseqs_3315_);
return v___x_3344_;
}
}
else
{
lean_dec_ref(v___x_3331_);
lean_dec_ref(v___x_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_diseqs_3315_);
lean_dec_ref(v_uppers_3314_);
return v___x_3339_;
}
}
else
{
lean_dec_ref(v___x_3331_);
lean_dec_ref(v___x_3330_);
lean_dec_ref(v___x_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_diseqs_3315_);
lean_dec_ref(v_uppers_3314_);
return v___x_3333_;
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v_diseqs_3315_);
lean_dec_ref(v_uppers_3314_);
lean_dec_ref(v_lowers_3313_);
lean_dec_ref(v_dvds_3312_);
v_a_3384_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3323_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3323_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
else
{
lean_dec_ref(v_diseqs_3315_);
lean_dec_ref(v_uppers_3314_);
lean_dec_ref(v_lowers_3313_);
lean_dec_ref(v_dvds_3312_);
return v___x_3322_;
}
}
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
lean_dec_ref(v_diseqs_3315_);
lean_dec_ref(v_uppers_3314_);
lean_dec_ref(v_lowers_3313_);
lean_dec_ref(v_dvds_3312_);
lean_dec_ref(v_vars_x27_3311_);
v___x_3392_ = lean_box(0);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3392_);
v___x_3394_ = v___x_3308_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
v_a_3397_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3305_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3305_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec(v_a_3410_);
lean_dec_ref(v_a_3409_);
lean_dec(v_a_3408_);
lean_dec_ref(v_a_3407_);
lean_dec(v_a_3406_);
lean_dec(v_a_3405_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object* v_00_u03b2_3417_, lean_object* v_00_u03c3_3418_, lean_object* v_pm_3419_, lean_object* v_f_3420_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_pm_3419_, v_f_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object* v_cls_3422_, lean_object* v_msg_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3422_, v_msg_3423_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object* v_cls_3436_, lean_object* v_msg_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(v_cls_3436_, v_msg_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(lean_object* v_pm_3450_, lean_object* v_f_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2___redArg(v_f_3451_, v_pm_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(lean_object* v_00_u03b2_3453_, lean_object* v_00_u03c3_3454_, lean_object* v_pm_3455_, lean_object* v_f_3456_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2___redArg(v_f_3456_, v_pm_3455_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3458_, lean_object* v_00_u03b2_3459_, lean_object* v_00_u03c3_3460_, lean_object* v_f_3461_, lean_object* v_n_3462_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2___redArg(v_f_3461_, v_n_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21(lean_object* v_00_u03b1_3464_, lean_object* v_00_u03b2_3465_, lean_object* v_00_u03c3_3466_, lean_object* v_f_3467_, size_t v_sz_3468_, size_t v_i_3469_, lean_object* v_bs_3470_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___redArg(v_f_3467_, v_sz_3468_, v_i_3469_, v_bs_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21___boxed(lean_object* v_00_u03b1_3472_, lean_object* v_00_u03b2_3473_, lean_object* v_00_u03c3_3474_, lean_object* v_f_3475_, lean_object* v_sz_3476_, lean_object* v_i_3477_, lean_object* v_bs_3478_){
_start:
{
size_t v_sz_boxed_3479_; size_t v_i_boxed_3480_; lean_object* v_res_3481_; 
v_sz_boxed_3479_ = lean_unbox_usize(v_sz_3476_);
lean_dec(v_sz_3476_);
v_i_boxed_3480_ = lean_unbox_usize(v_i_3477_);
lean_dec(v_i_3477_);
v_res_3481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__21(v_00_u03b1_3472_, v_00_u03b2_3473_, v_00_u03c3_3474_, v_f_3475_, v_sz_boxed_3479_, v_i_boxed_3480_, v_bs_3478_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22(lean_object* v_00_u03b1_3482_, lean_object* v_00_u03b2_3483_, lean_object* v_f_3484_, lean_object* v_as_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___redArg(v_f_3484_, v_as_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22___boxed(lean_object* v_00_u03b1_3487_, lean_object* v_00_u03b2_3488_, lean_object* v_f_3489_, lean_object* v_as_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22(v_00_u03b1_3487_, v_00_u03b2_3488_, v_f_3489_, v_as_3490_);
lean_dec_ref(v_as_3490_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42(lean_object* v_00_u03b1_3492_, lean_object* v_00_u03b2_3493_, lean_object* v_f_3494_, lean_object* v_as_3495_, lean_object* v_i_3496_, lean_object* v_acc_3497_, lean_object* v_hle_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___redArg(v_f_3494_, v_as_3495_, v_i_3496_, v_acc_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42___boxed(lean_object* v_00_u03b1_3500_, lean_object* v_00_u03b2_3501_, lean_object* v_f_3502_, lean_object* v_as_3503_, lean_object* v_i_3504_, lean_object* v_acc_3505_, lean_object* v_hle_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__2_spec__22_spec__42(v_00_u03b1_3500_, v_00_u03b2_3501_, v_f_3502_, v_as_3503_, v_i_3504_, v_acc_3505_, v_hle_3506_);
lean_dec_ref(v_as_3503_);
return v_res_3507_;
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
