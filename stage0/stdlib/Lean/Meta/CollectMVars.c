// Lean compiler output
// Module: Lean.Meta.CollectMVars
// Imports: public import Lean.Util.CollectMVars public import Lean.Meta.Basic
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
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_getMVars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getMVars___closed__0;
static lean_once_cell_t l_Lean_Meta_getMVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getMVars___closed__1;
static lean_once_cell_t l_Lean_Meta_getMVars___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getMVars___closed__2;
static const lean_array_object l_Lean_Meta_getMVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_getMVars___closed__3 = (const lean_object*)&l_Lean_Meta_getMVars___closed__3_value;
static lean_once_cell_t l_Lean_Meta_getMVars___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getMVars___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0;
static lean_once_cell_t l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__12(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13_spec__15(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9_spec__15(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_30_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(lean_object* v_mvarId_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; lean_object* v_mctx_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_st_ref_get(v___y_47_);
v_mctx_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc_ref(v_mctx_50_);
lean_dec(v___x_49_);
v___x_51_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_50_, v_mvarId_46_);
lean_dec_ref(v_mctx_50_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg___boxed(lean_object* v_mvarId_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v_mvarId_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec(v_mvarId_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(lean_object* v_mvarId_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v_mvarId_57_, v___y_60_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___boxed(lean_object* v_mvarId_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(v_mvarId_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec(v_mvarId_65_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars(lean_object* v_e_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_73_, v_a_76_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_82_; lean_object* v_result_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_result_86_; lean_object* v_lower_88_; lean_object* v_upper_89_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v___x_80_, 1);
v___x_82_ = lean_st_ref_get(v_a_74_);
v_result_83_ = lean_ctor_get(v___x_82_, 1);
lean_inc_ref(v_result_83_);
v___x_84_ = l_Lean_Expr_collectMVars(v___x_82_, v_a_81_);
lean_inc_ref(v___x_84_);
v___x_85_ = lean_st_ref_swap(v_a_74_, v___x_84_);
lean_dec(v___x_85_);
v_result_86_ = lean_ctor_get(v___x_84_, 1);
lean_inc_ref(v_result_86_);
lean_dec_ref(v___x_84_);
v___x_101_ = lean_array_get_size(v_result_83_);
lean_dec_ref(v_result_83_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_array_get_size(v_result_86_);
v___x_104_ = lean_nat_dec_le(v___x_101_, v___x_102_);
if (v___x_104_ == 0)
{
v_lower_88_ = v___x_101_;
v_upper_89_ = v___x_103_;
goto v___jp_87_;
}
else
{
v_lower_88_ = v___x_102_;
v_upper_89_ = v___x_103_;
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = l_Array_toSubarray___redArg(v_result_86_, v_lower_88_, v_upper_89_);
v___x_91_ = lean_box(0);
v___x_92_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v___x_90_, v___x_91_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v___x_92_, 0);
lean_dec(v_unused_100_);
v___x_94_ = v___x_92_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_dec(v___x_92_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_91_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_91_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
else
{
return v___x_92_;
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_105_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_80_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_80_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(lean_object* v_a_113_, lean_object* v_b_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_array_121_; lean_object* v_start_122_; lean_object* v_stop_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_152_; 
v_array_121_ = lean_ctor_get(v_a_113_, 0);
v_start_122_ = lean_ctor_get(v_a_113_, 1);
v_stop_123_ = lean_ctor_get(v_a_113_, 2);
v_isSharedCheck_152_ = !lean_is_exclusive(v_a_113_);
if (v_isSharedCheck_152_ == 0)
{
v___x_125_ = v_a_113_;
v_isShared_126_ = v_isSharedCheck_152_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_stop_123_);
lean_inc(v_start_122_);
lean_inc(v_array_121_);
lean_dec(v_a_113_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_152_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_lt(v_start_122_, v_stop_123_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
lean_del_object(v___x_125_);
lean_dec(v_stop_123_);
lean_dec(v_start_122_);
lean_dec_ref(v_array_121_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v_b_114_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_array_fget_borrowed(v_array_121_, v_start_122_);
v___x_130_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v___x_129_, v___y_117_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
v___x_132_ = lean_box(0);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_add(v_start_122_, v___x_133_);
lean_dec(v_start_122_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_134_);
v___x_136_ = v___x_125_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_array_121_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_stop_123_);
v___x_136_ = v_reuseFailAlloc_143_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
if (lean_obj_tag(v_a_131_) == 0)
{
v_a_113_ = v___x_136_;
v_b_114_ = v___x_132_;
goto _start;
}
else
{
lean_object* v_val_138_; lean_object* v_mvarIdPending_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_val_138_ = lean_ctor_get(v_a_131_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v_a_131_, 1);
v_mvarIdPending_139_ = lean_ctor_get(v_val_138_, 1);
lean_inc(v_mvarIdPending_139_);
lean_dec(v_val_138_);
v___x_140_ = l_Lean_mkMVar(v_mvarIdPending_139_);
v___x_141_ = l_Lean_Meta_collectMVars(v___x_140_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_dec_ref_known(v___x_141_, 1);
v_a_113_ = v___x_136_;
v_b_114_ = v___x_132_;
goto _start;
}
else
{
lean_dec_ref(v___x_136_);
return v___x_141_;
}
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_del_object(v___x_125_);
lean_dec(v_stop_123_);
lean_dec(v_start_122_);
lean_dec_ref(v_array_121_);
v_a_144_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_130_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_130_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___boxed(lean_object* v_a_153_, lean_object* v_b_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_153_, v_b_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars___boxed(lean_object* v_e_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Meta_collectMVars(v_e_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(lean_object* v_inst_170_, lean_object* v_R_171_, lean_object* v_a_172_, lean_object* v_b_173_, lean_object* v_c_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_172_, v_b_173_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___boxed(lean_object* v_inst_182_, lean_object* v_R_183_, lean_object* v_a_184_, lean_object* v_b_185_, lean_object* v_c_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(v_inst_182_, v_R_183_, v_a_184_, v_b_185_, v_c_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
return v_res_193_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__0(void){
_start:
{
lean_object* v_cellCount_194_; lean_object* v___x_195_; 
v_cellCount_194_ = lean_unsigned_to_nat(16u);
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__1(void){
_start:
{
lean_object* v_cellCount_196_; lean_object* v___x_197_; 
v_cellCount_196_ = lean_unsigned_to_nat(16u);
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_198_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__1, &l_Lean_Meta_getMVars___closed__1_once, _init_l_Lean_Meta_getMVars___closed__1);
v___x_199_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__0, &l_Lean_Meta_getMVars___closed__0_once, _init_l_Lean_Meta_getMVars___closed__0);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_198_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__4(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__3));
v___x_205_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__2, &l_Lean_Meta_getMVars___closed__2_once, _init_l_Lean_Meta_getMVars___closed__2);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars(lean_object* v_e_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__4, &l_Lean_Meta_getMVars___closed__4_once, _init_l_Lean_Meta_getMVars___closed__4);
v___x_214_ = lean_st_mk_ref(v___x_213_);
v___x_215_ = l_Lean_Meta_collectMVars(v_e_207_, v___x_214_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_224_; 
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; 
v_unused_225_ = lean_ctor_get(v___x_215_, 0);
lean_dec(v_unused_225_);
v___x_217_ = v___x_215_;
v_isShared_218_ = v_isSharedCheck_224_;
goto v_resetjp_216_;
}
else
{
lean_dec(v___x_215_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_224_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v_result_220_; lean_object* v___x_222_; 
v___x_219_ = lean_st_ref_get(v___x_214_);
lean_dec(v___x_214_);
v_result_220_ = lean_ctor_get(v___x_219_, 1);
lean_inc_ref(v_result_220_);
lean_dec(v___x_219_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v_result_220_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_result_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec(v___x_214_);
v_a_226_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_215_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_215_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars___boxed(lean_object* v_e_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_getMVars(v_e_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_241_, lean_object* v_i_242_, lean_object* v_k_243_){
_start:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_array_get_size(v_keys_241_);
v___x_245_ = lean_nat_dec_lt(v_i_242_, v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v_i_242_);
return v___x_245_;
}
else
{
lean_object* v_k_x27_246_; uint8_t v___x_247_; 
v_k_x27_246_ = lean_array_fget_borrowed(v_keys_241_, v_i_242_);
v___x_247_ = l_Lean_instBEqMVarId_beq(v_k_243_, v_k_x27_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_add(v_i_242_, v___x_248_);
lean_dec(v_i_242_);
v_i_242_ = v___x_249_;
goto _start;
}
else
{
lean_dec(v_i_242_);
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_251_, lean_object* v_i_252_, lean_object* v_k_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_251_, v_i_252_, v_k_253_);
lean_dec(v_k_253_);
lean_dec_ref(v_keys_251_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_256_, size_t v_x_257_, lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v_es_259_; lean_object* v___x_260_; size_t v___x_261_; size_t v___x_262_; lean_object* v_j_263_; lean_object* v___x_264_; 
v_es_259_ = lean_ctor_get(v_x_256_, 0);
v___x_260_ = lean_box(2);
v___x_261_ = ((size_t)31ULL);
v___x_262_ = lean_usize_land(v_x_257_, v___x_261_);
v_j_263_ = lean_usize_to_nat(v___x_262_);
v___x_264_ = lean_array_get_borrowed(v___x_260_, v_es_259_, v_j_263_);
lean_dec(v_j_263_);
switch(lean_obj_tag(v___x_264_))
{
case 0:
{
lean_object* v_key_265_; uint8_t v___x_266_; 
v_key_265_ = lean_ctor_get(v___x_264_, 0);
v___x_266_ = l_Lean_instBEqMVarId_beq(v_x_258_, v_key_265_);
return v___x_266_;
}
case 1:
{
lean_object* v_node_267_; size_t v___x_268_; size_t v___x_269_; 
v_node_267_ = lean_ctor_get(v___x_264_, 0);
v___x_268_ = ((size_t)5ULL);
v___x_269_ = lean_usize_shift_right(v_x_257_, v___x_268_);
v_x_256_ = v_node_267_;
v_x_257_ = v___x_269_;
goto _start;
}
default: 
{
uint8_t v___x_271_; 
v___x_271_ = 0;
return v___x_271_;
}
}
}
else
{
lean_object* v_ks_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_ks_272_ = lean_ctor_get(v_x_256_, 0);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_272_, v___x_273_, v_x_258_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
size_t v_x_1293__boxed_278_; uint8_t v_res_279_; lean_object* v_r_280_; 
v_x_1293__boxed_278_ = lean_unbox_usize(v_x_276_);
lean_dec(v_x_276_);
v_res_279_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_275_, v_x_1293__boxed_278_, v_x_277_);
lean_dec(v_x_277_);
lean_dec_ref(v_x_275_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
uint64_t v___x_283_; size_t v___x_284_; uint8_t v___x_285_; 
v___x_283_ = l_Lean_instHashableMVarId_hash(v_x_282_);
v___x_284_ = lean_uint64_to_usize(v___x_283_);
v___x_285_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_281_, v___x_284_, v_x_282_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg___boxed(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_286_, v_x_287_);
lean_dec(v_x_287_);
lean_dec_ref(v_x_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(lean_object* v_mvarId_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; lean_object* v_mctx_294_; lean_object* v_dAssignment_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_293_ = lean_st_ref_get(v___y_291_);
v_mctx_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_ref(v_mctx_294_);
lean_dec(v___x_293_);
v_dAssignment_295_ = lean_ctor_get(v_mctx_294_, 9);
lean_inc_ref(v_dAssignment_295_);
lean_dec_ref(v_mctx_294_);
v___x_296_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_295_, v_mvarId_290_);
lean_dec_ref(v_dAssignment_295_);
v___x_297_ = lean_box(v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(lean_object* v_mvarId_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec(v_mvarId_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(lean_object* v_as_303_, size_t v_i_304_, size_t v_stop_305_, lean_object* v_b_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_a_313_; uint8_t v___x_317_; 
v___x_317_ = lean_usize_dec_eq(v_i_304_, v_stop_305_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_321_; 
v___x_318_ = lean_array_uget_borrowed(v_as_303_, v_i_304_);
v___x_321_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v___x_318_, v___y_308_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; uint8_t v___x_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_unbox(v_a_322_);
lean_dec(v_a_322_);
if (v___x_323_ == 0)
{
goto v___jp_319_;
}
else
{
v_a_313_ = v_b_306_;
goto v___jp_312_;
}
}
else
{
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_324_; uint8_t v___x_325_; 
v_a_324_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_321_, 1);
v___x_325_ = lean_unbox(v_a_324_);
lean_dec(v_a_324_);
if (v___x_325_ == 0)
{
v_a_313_ = v_b_306_;
goto v___jp_312_;
}
else
{
goto v___jp_319_;
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v_b_306_);
v_a_326_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_321_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
v___jp_319_:
{
lean_object* v___x_320_; 
lean_inc(v___x_318_);
v___x_320_ = lean_array_push(v_b_306_, v___x_318_);
v_a_313_ = v___x_320_;
goto v___jp_312_;
}
}
else
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v_b_306_);
return v___x_334_;
}
v___jp_312_:
{
size_t v___x_314_; size_t v___x_315_; 
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_i_304_, v___x_314_);
v_i_304_ = v___x_315_;
v_b_306_ = v_a_313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1___boxed(lean_object* v_as_335_, lean_object* v_i_336_, lean_object* v_stop_337_, lean_object* v_b_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_337_);
lean_dec(v_stop_337_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_335_, v_i_boxed_344_, v_stop_boxed_345_, v_b_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v_as_335_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object* v_e_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Meta_getMVars(v_e_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_375_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_375_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_375_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_375_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_array_get_size(v_a_354_);
v___x_360_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__3));
v___x_361_ = lean_nat_dec_lt(v___x_358_, v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_a_354_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_360_);
v___x_363_ = v___x_356_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
else
{
uint8_t v___x_365_; 
v___x_365_ = lean_nat_dec_le(v___x_359_, v___x_359_);
if (v___x_365_ == 0)
{
if (v___x_361_ == 0)
{
lean_object* v___x_367_; 
lean_dec(v_a_354_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_360_);
v___x_367_ = v___x_356_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_360_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
else
{
size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; 
lean_del_object(v___x_356_);
v___x_369_ = ((size_t)0ULL);
v___x_370_ = lean_usize_of_nat(v___x_359_);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_354_, v___x_369_, v___x_370_, v___x_360_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_354_);
return v___x_371_;
}
}
else
{
size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; 
lean_del_object(v___x_356_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = lean_usize_of_nat(v___x_359_);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_354_, v___x_372_, v___x_373_, v___x_360_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_354_);
return v___x_374_;
}
}
}
}
else
{
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object* v_e_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_getMVarsNoDelayed(v_e_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(lean_object* v_mvarId_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_383_, v___y_385_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(lean_object* v_mvarId_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(v_mvarId_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v_mvarId_390_);
return v_res_396_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(lean_object* v_00_u03b2_397_, lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_398_, v_x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_401_, lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(v_00_u03b2_401_, v_x_402_, v_x_403_);
lean_dec(v_x_403_);
lean_dec_ref(v_x_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_406_, lean_object* v_x_407_, size_t v_x_408_, lean_object* v_x_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_407_, v_x_408_, v_x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
size_t v_x_1498__boxed_415_; uint8_t v_res_416_; lean_object* v_r_417_; 
v_x_1498__boxed_415_ = lean_unbox_usize(v_x_413_);
lean_dec(v_x_413_);
v_res_416_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(v_00_u03b2_411_, v_x_412_, v_x_1498__boxed_415_, v_x_414_);
lean_dec(v_x_414_);
lean_dec_ref(v_x_412_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_418_, lean_object* v_keys_419_, lean_object* v_vals_420_, lean_object* v_heq_421_, lean_object* v_i_422_, lean_object* v_k_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_419_, v_i_422_, v_k_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_425_, lean_object* v_keys_426_, lean_object* v_vals_427_, lean_object* v_heq_428_, lean_object* v_i_429_, lean_object* v_k_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_425_, v_keys_426_, v_vals_427_, v_heq_428_, v_i_429_, v_k_430_);
lean_dec(v_k_430_);
lean_dec_ref(v_vals_427_);
lean_dec_ref(v_keys_426_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v_x_433_);
return v___x_441_;
}
else
{
lean_object* v_head_442_; lean_object* v_tail_443_; lean_object* v_type_444_; lean_object* v___x_445_; 
v_head_442_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_head_442_);
v_tail_443_ = lean_ctor_get(v_x_434_, 1);
lean_inc(v_tail_443_);
lean_dec_ref_known(v_x_434_, 2);
v_type_444_ = lean_ctor_get(v_head_442_, 1);
lean_inc_ref(v_type_444_);
lean_dec(v_head_442_);
v___x_445_ = l_Lean_Meta_collectMVars(v_type_444_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
v_x_433_ = v_a_446_;
v_x_434_ = v_tail_443_;
goto _start;
}
else
{
lean_dec(v_tail_443_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_448_, v_x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_x_457_);
return v___x_465_;
}
else
{
lean_object* v_head_466_; lean_object* v_tail_467_; lean_object* v___y_469_; lean_object* v_type_472_; lean_object* v_ctors_473_; lean_object* v___x_474_; 
v_head_466_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_head_466_);
v_tail_467_ = lean_ctor_get(v_x_458_, 1);
lean_inc(v_tail_467_);
lean_dec_ref_known(v_x_458_, 2);
v_type_472_ = lean_ctor_get(v_head_466_, 1);
lean_inc_ref(v_type_472_);
v_ctors_473_ = lean_ctor_get(v_head_466_, 2);
lean_inc(v_ctors_473_);
lean_dec(v_head_466_);
v___x_474_ = l_Lean_Meta_collectMVars(v_type_472_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_a_475_, v_ctors_473_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
v___y_469_ = v___x_476_;
goto v___jp_468_;
}
else
{
lean_dec(v_ctors_473_);
v___y_469_ = v___x_474_;
goto v___jp_468_;
}
v___jp_468_:
{
if (lean_obj_tag(v___y_469_) == 0)
{
lean_object* v_a_470_; 
v_a_470_ = lean_ctor_get(v___y_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___y_469_, 1);
v_x_457_ = v_a_470_;
v_x_458_ = v_tail_467_;
goto _start;
}
else
{
lean_dec(v_tail_467_);
return v___y_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_477_, v_x_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_x_486_);
return v___x_494_;
}
else
{
lean_object* v_head_495_; lean_object* v_tail_496_; lean_object* v___y_498_; lean_object* v_toConstantVal_501_; lean_object* v_value_502_; lean_object* v_type_503_; lean_object* v___x_504_; 
v_head_495_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_head_495_);
v_tail_496_ = lean_ctor_get(v_x_487_, 1);
lean_inc(v_tail_496_);
lean_dec_ref_known(v_x_487_, 2);
v_toConstantVal_501_ = lean_ctor_get(v_head_495_, 0);
lean_inc_ref(v_toConstantVal_501_);
v_value_502_ = lean_ctor_get(v_head_495_, 1);
lean_inc_ref(v_value_502_);
lean_dec(v_head_495_);
v_type_503_ = lean_ctor_get(v_toConstantVal_501_, 2);
lean_inc_ref(v_type_503_);
lean_dec_ref(v_toConstantVal_501_);
v___x_504_ = l_Lean_Meta_collectMVars(v_type_503_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_505_; 
lean_dec_ref_known(v___x_504_, 1);
v___x_505_ = l_Lean_Meta_collectMVars(v_value_502_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
v___y_498_ = v___x_505_;
goto v___jp_497_;
}
else
{
lean_dec_ref(v_value_502_);
v___y_498_ = v___x_504_;
goto v___jp_497_;
}
v___jp_497_:
{
if (lean_obj_tag(v___y_498_) == 0)
{
lean_object* v_a_499_; 
v_a_499_ = lean_ctor_get(v___y_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___y_498_, 1);
v_x_486_ = v_a_499_;
v_x_487_ = v_tail_496_;
goto _start;
}
else
{
lean_dec(v_tail_496_);
return v___y_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_506_, v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(lean_object* v_d_515_, lean_object* v_a_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
switch(lean_obj_tag(v_d_515_))
{
case 0:
{
lean_object* v_val_523_; lean_object* v_toConstantVal_524_; lean_object* v_type_525_; lean_object* v___x_526_; 
v_val_523_ = lean_ctor_get(v_d_515_, 0);
lean_inc_ref(v_val_523_);
lean_dec_ref_known(v_d_515_, 1);
v_toConstantVal_524_ = lean_ctor_get(v_val_523_, 0);
lean_inc_ref(v_toConstantVal_524_);
lean_dec_ref(v_val_523_);
v_type_525_ = lean_ctor_get(v_toConstantVal_524_, 2);
lean_inc_ref(v_type_525_);
lean_dec_ref(v_toConstantVal_524_);
v___x_526_ = l_Lean_Meta_collectMVars(v_type_525_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_526_;
}
case 4:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v_a_516_);
return v___x_527_;
}
case 5:
{
lean_object* v_defns_528_; lean_object* v___x_529_; 
v_defns_528_ = lean_ctor_get(v_d_515_, 0);
lean_inc(v_defns_528_);
lean_dec_ref_known(v_d_515_, 1);
v___x_529_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_a_516_, v_defns_528_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_529_;
}
case 6:
{
lean_object* v_types_530_; lean_object* v___x_531_; 
v_types_530_ = lean_ctor_get(v_d_515_, 2);
lean_inc(v_types_530_);
lean_dec_ref_known(v_d_515_, 3);
v___x_531_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_a_516_, v_types_530_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_531_;
}
default: 
{
lean_object* v_val_532_; lean_object* v_toConstantVal_533_; lean_object* v_value_534_; lean_object* v_type_535_; lean_object* v___x_536_; 
v_val_532_ = lean_ctor_get(v_d_515_, 0);
lean_inc_ref(v_val_532_);
lean_dec(v_d_515_);
v_toConstantVal_533_ = lean_ctor_get(v_val_532_, 0);
lean_inc_ref(v_toConstantVal_533_);
v_value_534_ = lean_ctor_get(v_val_532_, 1);
lean_inc_ref(v_value_534_);
lean_dec_ref(v_val_532_);
v_type_535_ = lean_ctor_get(v_toConstantVal_533_, 2);
lean_inc_ref(v_type_535_);
lean_dec_ref(v_toConstantVal_533_);
v___x_536_ = l_Lean_Meta_collectMVars(v_type_535_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; 
lean_dec_ref_known(v___x_536_, 1);
v___x_537_ = l_Lean_Meta_collectMVars(v_value_534_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_537_;
}
else
{
lean_dec_ref(v_value_534_);
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(lean_object* v_d_538_, lean_object* v_a_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_538_, v_a_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object* v_d_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_box(0);
v___x_555_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_547_, v___x_554_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object* v_d_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Meta_collectMVarsAtDecl(v_d_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object* v_d_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__4, &l_Lean_Meta_getMVars___closed__4_once, _init_l_Lean_Meta_getMVars___closed__4);
v___x_571_ = lean_st_mk_ref(v___x_570_);
v___x_572_ = l_Lean_Meta_collectMVarsAtDecl(v_d_564_, v___x_571_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_581_; 
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v___x_572_, 0);
lean_dec(v_unused_582_);
v___x_574_ = v___x_572_;
v_isShared_575_ = v_isSharedCheck_581_;
goto v_resetjp_573_;
}
else
{
lean_dec(v___x_572_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_581_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v_result_577_; lean_object* v___x_579_; 
v___x_576_ = lean_st_ref_get(v___x_571_);
lean_dec(v___x_571_);
v_result_577_ = lean_ctor_get(v___x_576_, 1);
lean_inc_ref(v_result_577_);
lean_dec(v___x_576_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v_result_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_result_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v___x_571_);
v_a_583_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_572_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_572_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object* v_d_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Meta_getMVarsAtDecl(v_d_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(lean_object* v_m_598_, lean_object* v_query_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v_zero_603_; uint8_t v_isZero_604_; 
v_zero_603_ = lean_unsigned_to_nat(0u);
v_isZero_604_ = lean_nat_dec_eq(v_x_601_, v_zero_603_);
if (v_isZero_604_ == 1)
{
lean_dec(v_x_602_);
lean_dec(v_x_601_);
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_box(2);
return v___x_605_;
}
else
{
lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_val_606_ = lean_ctor_get(v_x_600_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v_x_600_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_dec(v_x_600_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_val_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_keyArray_614_; lean_object* v_valueArray_615_; lean_object* v___x_616_; uint8_t v_isSome_617_; 
v_keyArray_614_ = lean_ctor_get(v_m_598_, 1);
v_valueArray_615_ = lean_ctor_get(v_m_598_, 2);
v___x_616_ = lean_array_fget_borrowed(v_keyArray_614_, v_x_602_);
v_isSome_617_ = lean_noption_is_some(v___x_616_);
if (v_isSome_617_ == 0)
{
lean_dec(v_x_601_);
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_x_602_);
return v___x_618_;
}
else
{
lean_object* v_val_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_x_602_);
v_val_619_ = lean_ctor_get(v_x_600_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v_x_600_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_val_619_);
lean_dec(v_x_600_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_val_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v_one_627_; lean_object* v_n_628_; lean_object* v___y_630_; 
v_one_627_ = lean_unsigned_to_nat(1u);
v_n_628_ = lean_nat_sub(v_x_601_, v_one_627_);
lean_dec(v_x_601_);
if (v_isSome_617_ == 0)
{
goto v___jp_636_;
}
else
{
lean_object* v___x_638_; uint8_t v_isSome_639_; 
v___x_638_ = lean_array_fget_borrowed(v_valueArray_615_, v_x_602_);
v_isSome_639_ = lean_noption_is_some(v___x_638_);
if (v_isSome_639_ == 0)
{
goto v___jp_636_;
}
else
{
lean_object* v_val_640_; uint8_t v___x_641_; 
lean_inc(v___x_616_);
v_val_640_ = lean_noption_get(v___x_616_);
v___x_641_ = l_Lean_instBEqMVarId_beq(v_val_640_, v_query_599_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
lean_dec(v_val_640_);
v___x_642_ = lean_array_get_size(v_keyArray_614_);
v___x_643_ = lean_nat_add(v_x_602_, v_one_627_);
lean_dec(v_x_602_);
v___x_644_ = lean_nat_dec_lt(v___x_643_, v___x_642_);
if (v___x_644_ == 0)
{
lean_dec(v___x_643_);
v_x_601_ = v_n_628_;
v_x_602_ = v_zero_603_;
goto _start;
}
else
{
v_x_601_ = v_n_628_;
v_x_602_ = v___x_643_;
goto _start;
}
}
else
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_dec(v_n_628_);
lean_dec(v_x_600_);
lean_inc(v___x_638_);
v_val_647_ = lean_noption_get(v___x_638_);
v___x_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_648_, 0, v_x_602_);
lean_ctor_set(v___x_648_, 1, v_val_640_);
lean_ctor_set(v___x_648_, 2, v_val_647_);
return v___x_648_;
}
}
}
v___jp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = lean_array_get_size(v_keyArray_614_);
v___x_632_ = lean_nat_add(v_x_602_, v_one_627_);
lean_dec(v_x_602_);
v___x_633_ = lean_nat_dec_lt(v___x_632_, v___x_631_);
if (v___x_633_ == 0)
{
lean_dec(v___x_632_);
v_x_600_ = v___y_630_;
v_x_601_ = v_n_628_;
v_x_602_ = v_zero_603_;
goto _start;
}
else
{
v_x_600_ = v___y_630_;
v_x_601_ = v_n_628_;
v_x_602_ = v___x_632_;
goto _start;
}
}
v___jp_636_:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_637_; 
lean_inc(v_x_602_);
v___x_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_637_, 0, v_x_602_);
v___y_630_ = v___x_637_;
goto v___jp_629_;
}
else
{
v___y_630_ = v_x_600_;
goto v___jp_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(lean_object* v_m_649_, lean_object* v_query_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_m_649_, v_query_650_, v_x_651_, v_x_652_, v_x_653_);
lean_dec(v_query_650_);
lean_dec_ref(v_m_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(lean_object* v_m_655_, lean_object* v_query_656_){
_start:
{
lean_object* v_keyArray_657_; lean_object* v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; uint64_t v_fold_662_; uint64_t v___x_663_; uint64_t v___x_664_; uint64_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_keyArray_657_ = lean_ctor_get(v_m_655_, 1);
v___x_658_ = lean_array_get_size(v_keyArray_657_);
v___x_659_ = l_Lean_instHashableMVarId_hash(v_query_656_);
v___x_660_ = 32ULL;
v___x_661_ = lean_uint64_shift_right(v___x_659_, v___x_660_);
v_fold_662_ = lean_uint64_xor(v___x_659_, v___x_661_);
v___x_663_ = 16ULL;
v___x_664_ = lean_uint64_shift_right(v_fold_662_, v___x_663_);
v___x_665_ = lean_uint64_xor(v_fold_662_, v___x_664_);
v___x_666_ = lean_uint64_to_usize(v___x_665_);
v___x_667_ = lean_usize_of_nat(v___x_658_);
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_sub(v___x_667_, v___x_668_);
v___x_670_ = lean_usize_land(v___x_666_, v___x_669_);
v___x_671_ = lean_usize_to_nat(v___x_670_);
v___x_672_ = lean_box(0);
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_m_655_, v_query_656_, v___x_672_, v___x_658_, v___x_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg___boxed(lean_object* v_m_674_, lean_object* v_query_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_674_, v_query_675_);
lean_dec(v_query_675_);
lean_dec_ref(v_m_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(lean_object* v_mvarId_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; lean_object* v_mctx_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_680_ = lean_st_ref_get(v___y_678_);
v_mctx_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref(v_mctx_681_);
lean_dec(v___x_680_);
v___x_682_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_681_, v_mvarId_677_);
lean_dec_ref(v_mctx_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(lean_object* v_mvarId_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec(v_mvarId_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(lean_object* v_mvarId_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v_mctx_692_; lean_object* v_eAssignment_693_; lean_object* v_dAssignment_694_; uint8_t v___x_695_; 
v___x_691_ = lean_st_ref_get(v___y_689_);
v_mctx_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_mctx_692_);
lean_dec(v___x_691_);
v_eAssignment_693_ = lean_ctor_get(v_mctx_692_, 8);
lean_inc_ref(v_eAssignment_693_);
v_dAssignment_694_ = lean_ctor_get(v_mctx_692_, 9);
lean_inc_ref(v_dAssignment_694_);
lean_dec_ref(v_mctx_692_);
v___x_695_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_eAssignment_693_, v_mvarId_688_);
lean_dec_ref(v_eAssignment_693_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_694_, v_mvarId_688_);
lean_dec_ref(v_dAssignment_694_);
v___x_697_ = lean_box(v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec_ref(v_dAssignment_694_);
v___x_699_ = lean_box(v___x_695_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(lean_object* v_mvarId_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_mvarId_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec(v_mvarId_701_);
return v_res_704_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_Lean_maxRecDepthErrorMessage;
v___x_711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__3);
v___x_713_ = l_Lean_MessageData_ofFormat(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__4);
v___x_715_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__2));
v___x_716_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg(lean_object* v_ref_717_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___closed__5);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_ref_717_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg___boxed(lean_object* v_ref_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg(v_ref_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___redArg(lean_object* v_b_725_, lean_object* v_acc_726_, lean_object* v_i_727_){
_start:
{
lean_object* v___y_729_; lean_object* v_keyArray_737_; lean_object* v_valueArray_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_keyArray_737_ = lean_ctor_get(v_b_725_, 1);
v_valueArray_738_ = lean_ctor_get(v_b_725_, 2);
v___x_739_ = lean_array_get_size(v_keyArray_737_);
v___x_740_ = lean_nat_dec_lt(v_i_727_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v_i_727_);
return v_acc_726_;
}
else
{
lean_object* v___x_741_; uint8_t v_isSome_742_; 
v___x_741_ = lean_array_fget_borrowed(v_keyArray_737_, v_i_727_);
v_isSome_742_ = lean_noption_is_some(v___x_741_);
if (v_isSome_742_ == 0)
{
goto v___jp_733_;
}
else
{
lean_object* v___x_743_; uint8_t v_isSome_744_; 
v___x_743_ = lean_array_fget_borrowed(v_valueArray_738_, v_i_727_);
v_isSome_744_ = lean_noption_is_some(v___x_743_);
if (v_isSome_744_ == 0)
{
goto v___jp_733_;
}
else
{
lean_object* v_val_745_; lean_object* v_val_746_; lean_object* v_i_748_; lean_object* v___x_753_; 
lean_inc(v___x_741_);
v_val_745_ = lean_noption_get(v___x_741_);
lean_inc(v___x_743_);
v_val_746_ = lean_noption_get(v___x_743_);
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_acc_726_, v_val_745_);
switch(lean_obj_tag(v___x_753_))
{
case 0:
{
lean_object* v_index_754_; lean_object* v_size_755_; lean_object* v___x_756_; 
v_index_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_index_754_);
lean_dec_ref_known(v___x_753_, 3);
v_size_755_ = lean_ctor_get(v_acc_726_, 0);
lean_inc(v_size_755_);
v___x_756_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_726_, v_size_755_, v_index_754_, v_val_745_, v_val_746_);
lean_dec(v_index_754_);
v___y_729_ = v___x_756_;
goto v___jp_728_;
}
case 1:
{
lean_object* v_index_757_; 
v_index_757_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_index_757_);
lean_dec_ref_known(v___x_753_, 1);
v_i_748_ = v_index_757_;
goto v___jp_747_;
}
default: 
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_726_, v___x_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_index_760_; 
v_index_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_index_760_);
lean_dec_ref_known(v___x_759_, 1);
v_i_748_ = v_index_760_;
goto v___jp_747_;
}
else
{
lean_dec(v_val_746_);
lean_dec(v_val_745_);
v___y_729_ = v_acc_726_;
goto v___jp_728_;
}
}
}
v___jp_747_:
{
lean_object* v_size_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_size_749_ = lean_ctor_get(v_acc_726_, 0);
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v_size_749_, v___x_750_);
v___x_752_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_726_, v___x_751_, v_i_748_, v_val_745_, v_val_746_);
lean_dec(v_i_748_);
v___y_729_ = v___x_752_;
goto v___jp_728_;
}
}
}
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_add(v_i_727_, v___x_730_);
lean_dec(v_i_727_);
v_acc_726_ = v___y_729_;
v_i_727_ = v___x_731_;
goto _start;
}
v___jp_733_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v_i_727_, v___x_734_);
lean_dec(v_i_727_);
v_i_727_ = v___x_735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_b_761_, lean_object* v_acc_762_, lean_object* v_i_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___redArg(v_b_761_, v_acc_762_, v_i_763_);
lean_dec_ref(v_b_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___redArg(lean_object* v_init_765_, lean_object* v_b_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___redArg(v_b_766_, v_init_765_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___redArg___boxed(lean_object* v_init_769_, lean_object* v_b_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___redArg(v_init_769_, v_b_770_);
lean_dec_ref(v_b_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(lean_object* v_m_772_){
_start:
{
lean_object* v_keyArray_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_cellCount_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_target_780_; lean_object* v___x_781_; 
v_keyArray_773_ = lean_ctor_get(v_m_772_, 1);
v___x_774_ = lean_array_get_size(v_keyArray_773_);
v___x_775_ = lean_unsigned_to_nat(2u);
v_cellCount_776_ = lean_nat_mul(v___x_774_, v___x_775_);
v___x_777_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_776_);
v___x_778_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_776_);
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_776_);
v_target_780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_780_, 0, v___x_777_);
lean_ctor_set(v_target_780_, 1, v___x_778_);
lean_ctor_set(v_target_780_, 2, v___x_779_);
v___x_781_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___redArg(v_target_780_, v_m_772_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(lean_object* v_m_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_m_782_);
lean_dec_ref(v_m_782_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___redArg(lean_object* v_mvarId_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v_mctx_788_; lean_object* v_dAssignment_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_787_ = lean_st_ref_get(v___y_785_);
v_mctx_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_ref(v_mctx_788_);
lean_dec(v___x_787_);
v_dAssignment_789_ = lean_ctor_get(v_mctx_788_, 9);
lean_inc_ref(v_dAssignment_789_);
lean_dec_ref(v_mctx_788_);
v___x_790_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_789_, v_mvarId_784_);
lean_dec_ref(v_dAssignment_789_);
v___x_791_ = lean_box(v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___redArg___boxed(lean_object* v_mvarId_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___redArg(v_mvarId_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec(v_mvarId_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(uint8_t v_includeDelayed_797_, lean_object* v_as_798_, size_t v_sz_799_, size_t v_i_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_a_809_; uint8_t v___x_813_; 
v___x_813_ = lean_usize_dec_lt(v_i_800_, v_sz_799_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v_b_801_);
return v___x_814_;
}
else
{
lean_object* v_a_815_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v_i_819_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v_i_838_; lean_object* v___y_844_; 
v_a_815_ = lean_array_uget_borrowed(v_as_798_, v_i_800_);
if (v_includeDelayed_797_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___redArg(v_a_815_, v___y_804_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; uint8_t v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = lean_unbox(v_a_884_);
lean_dec(v_a_884_);
if (v___x_885_ == 0)
{
goto v___jp_854_;
}
else
{
v_a_809_ = v_b_801_;
goto v___jp_808_;
}
}
else
{
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_886_; uint8_t v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_883_, 1);
v___x_887_ = lean_unbox(v_a_886_);
lean_dec(v_a_886_);
if (v___x_887_ == 0)
{
v_a_809_ = v_b_801_;
goto v___jp_808_;
}
else
{
goto v___jp_854_;
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_b_801_);
v_a_888_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_883_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_883_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
else
{
goto v___jp_854_;
}
v___jp_816_:
{
lean_object* v_size_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_size_820_ = lean_ctor_get(v___y_817_, 0);
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v_size_820_, v___x_821_);
lean_inc(v_a_815_);
v___x_823_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_817_, v___x_822_, v_i_819_, v_a_815_, v___y_818_);
lean_dec(v_i_819_);
v_a_809_ = v___x_823_;
goto v___jp_808_;
}
v___jp_824_:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___y_826_, v_a_815_);
switch(lean_obj_tag(v___x_827_))
{
case 0:
{
lean_object* v_index_828_; lean_object* v_size_829_; lean_object* v___x_830_; 
v_index_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_index_828_);
lean_dec_ref_known(v___x_827_, 3);
v_size_829_ = lean_ctor_get(v___y_826_, 0);
lean_inc(v_size_829_);
lean_inc(v_a_815_);
v___x_830_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_826_, v_size_829_, v_index_828_, v_a_815_, v___y_825_);
lean_dec(v_index_828_);
v_a_809_ = v___x_830_;
goto v___jp_808_;
}
case 1:
{
lean_object* v_index_831_; 
v_index_831_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_index_831_);
lean_dec_ref_known(v___x_827_, 1);
v___y_817_ = v___y_826_;
v___y_818_ = v___y_825_;
v_i_819_ = v_index_831_;
goto v___jp_816_;
}
default: 
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_826_, v___x_832_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_index_834_; 
v_index_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_index_834_);
lean_dec_ref_known(v___x_833_, 1);
v___y_817_ = v___y_826_;
v___y_818_ = v___y_825_;
v_i_819_ = v_index_834_;
goto v___jp_816_;
}
else
{
v_a_809_ = v___y_826_;
goto v___jp_808_;
}
}
}
}
v___jp_835_:
{
lean_object* v_size_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_size_839_ = lean_ctor_get(v___y_836_, 0);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_size_839_, v___x_840_);
lean_inc(v_a_815_);
v___x_842_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_836_, v___x_841_, v_i_838_, v_a_815_, v___y_837_);
lean_dec(v_i_838_);
v_a_809_ = v___x_842_;
goto v___jp_808_;
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_b_801_);
lean_dec_ref(v_b_801_);
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_845_, v_a_815_);
switch(lean_obj_tag(v___x_846_))
{
case 0:
{
lean_object* v_index_847_; lean_object* v_size_848_; lean_object* v___x_849_; 
v_index_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_index_847_);
lean_dec_ref_known(v___x_846_, 3);
v_size_848_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_size_848_);
lean_inc(v_a_815_);
v___x_849_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_845_, v_size_848_, v_index_847_, v_a_815_, v___y_844_);
lean_dec(v_index_847_);
v_a_809_ = v___x_849_;
goto v___jp_808_;
}
case 1:
{
lean_object* v_index_850_; 
v_index_850_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_index_850_);
lean_dec_ref_known(v___x_846_, 1);
v___y_836_ = v___x_845_;
v___y_837_ = v___y_844_;
v_i_838_ = v_index_850_;
goto v___jp_835_;
}
default: 
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_845_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_index_853_; 
v_index_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_index_853_);
lean_dec_ref_known(v___x_852_, 1);
v___y_836_ = v___x_845_;
v___y_837_ = v___y_844_;
v_i_838_ = v_index_853_;
goto v___jp_835_;
}
else
{
v_a_809_ = v___x_845_;
goto v___jp_808_;
}
}
}
}
v___jp_854_:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_box(0);
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_b_801_, v_a_815_);
switch(lean_obj_tag(v___x_856_))
{
case 0:
{
lean_dec_ref_known(v___x_856_, 3);
v_a_809_ = v_b_801_;
goto v___jp_808_;
}
case 1:
{
lean_object* v_index_857_; lean_object* v_size_858_; lean_object* v_keyArray_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_index_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_index_857_);
lean_dec_ref_known(v___x_856_, 1);
v_size_858_ = lean_ctor_get(v_b_801_, 0);
v_keyArray_859_ = lean_ctor_get(v_b_801_, 1);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_nat_add(v_size_858_, v___x_860_);
v___x_862_ = lean_array_get_size(v_keyArray_859_);
v___x_863_ = lean_nat_dec_lt(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_dec(v___x_861_);
lean_dec(v_index_857_);
v___y_844_ = v___x_855_;
goto v___jp_843_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_864_ = lean_unsigned_to_nat(4u);
v___x_865_ = lean_nat_mul(v___x_861_, v___x_864_);
v___x_866_ = lean_unsigned_to_nat(3u);
v___x_867_ = lean_nat_mul(v___x_862_, v___x_866_);
v___x_868_ = lean_nat_dec_le(v___x_865_, v___x_867_);
lean_dec(v___x_867_);
lean_dec(v___x_865_);
if (v___x_868_ == 0)
{
lean_dec(v___x_861_);
lean_dec(v_index_857_);
v___y_844_ = v___x_855_;
goto v___jp_843_;
}
else
{
lean_object* v___x_869_; 
lean_inc(v_a_815_);
v___x_869_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_801_, v___x_861_, v_index_857_, v_a_815_, v___x_855_);
lean_dec(v_index_857_);
v_a_809_ = v___x_869_;
goto v___jp_808_;
}
}
}
default: 
{
lean_object* v_size_870_; lean_object* v_keyArray_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_size_870_ = lean_ctor_get(v_b_801_, 0);
v_keyArray_871_ = lean_ctor_get(v_b_801_, 1);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_add(v_size_870_, v___x_872_);
v___x_874_ = lean_array_get_size(v_keyArray_871_);
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec(v___x_873_);
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_b_801_);
lean_dec_ref(v_b_801_);
v___y_825_ = v___x_855_;
v___y_826_ = v___x_876_;
goto v___jp_824_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_877_ = lean_unsigned_to_nat(4u);
v___x_878_ = lean_nat_mul(v___x_873_, v___x_877_);
lean_dec(v___x_873_);
v___x_879_ = lean_unsigned_to_nat(3u);
v___x_880_ = lean_nat_mul(v___x_874_, v___x_879_);
v___x_881_ = lean_nat_dec_le(v___x_878_, v___x_880_);
lean_dec(v___x_880_);
lean_dec(v___x_878_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_b_801_);
lean_dec_ref(v_b_801_);
v___y_825_ = v___x_855_;
v___y_826_ = v___x_882_;
goto v___jp_824_;
}
else
{
v___y_825_ = v___x_855_;
v___y_826_ = v_b_801_;
goto v___jp_824_;
}
}
}
}
}
}
v___jp_808_:
{
size_t v___x_810_; size_t v___x_811_; 
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_add(v_i_800_, v___x_810_);
v_i_800_ = v___x_811_;
v_b_801_ = v_a_809_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object* v_includeDelayed_896_, lean_object* v_as_897_, lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_includeDelayed_boxed_907_; size_t v_sz_boxed_908_; size_t v_i_boxed_909_; lean_object* v_res_910_; 
v_includeDelayed_boxed_907_ = lean_unbox(v_includeDelayed_896_);
v_sz_boxed_908_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_909_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_includeDelayed_boxed_907_, v_as_897_, v_sz_boxed_908_, v_i_boxed_909_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v_as_897_);
return v_res_910_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0(void){
_start:
{
lean_object* v_cellCount_911_; lean_object* v___x_912_; 
v_cellCount_911_ = lean_unsigned_to_nat(16u);
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_911_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_913_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__1, &l_Lean_Meta_getMVars___closed__1_once, _init_l_Lean_Meta_getMVars___closed__1);
v___x_914_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_914_);
lean_ctor_set(v___x_916_, 2, v___x_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars(lean_object* v_e_917_, uint8_t v_includeDelayed_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Meta_getMVars(v_e_917_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; size_t v_sz_931_; size_t v___x_932_; lean_object* v___x_933_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = lean_st_ref_get(v_a_919_);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_930_ = lean_st_ref_swap(v_a_919_, v___x_929_);
lean_dec(v___x_930_);
v_sz_931_ = lean_array_size(v_a_926_);
v___x_932_ = ((size_t)0ULL);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_includeDelayed_918_, v_a_926_, v_sz_931_, v___x_932_, v___x_927_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_953_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_953_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_953_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_953_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_938_ = lean_st_ref_swap(v_a_919_, v_a_934_);
lean_dec(v___x_938_);
v___x_939_ = lean_array_get_size(v_a_926_);
v___x_940_ = lean_box(0);
v___x_941_ = lean_nat_dec_lt(v___x_928_, v___x_939_);
if (v___x_941_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v_a_926_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_940_);
v___x_943_ = v___x_936_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_940_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
else
{
uint8_t v___x_945_; 
v___x_945_ = lean_nat_dec_le(v___x_939_, v___x_939_);
if (v___x_945_ == 0)
{
if (v___x_941_ == 0)
{
lean_object* v___x_947_; 
lean_dec(v_a_926_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_940_);
v___x_947_ = v___x_936_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_940_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
else
{
size_t v___x_949_; lean_object* v___x_950_; 
lean_del_object(v___x_936_);
v___x_949_ = lean_usize_of_nat(v___x_939_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__4(v_a_926_, v___x_932_, v___x_949_, v___x_940_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_926_);
return v___x_950_;
}
}
else
{
size_t v___x_951_; lean_object* v___x_952_; 
lean_del_object(v___x_936_);
v___x_951_ = lean_usize_of_nat(v___x_939_);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__4(v_a_926_, v___x_932_, v___x_951_, v___x_940_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_926_);
return v___x_952_;
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_a_926_);
v_a_954_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_933_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_933_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_a_962_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_925_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_925_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__12(lean_object* v_init_970_, uint8_t v_includeDelayed_971_, lean_object* v_as_972_, size_t v_sz_973_, size_t v_i_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_lt(v_i_974_, v_sz_973_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_b_975_);
return v___x_983_;
}
else
{
lean_object* v_snd_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1018_; 
v_snd_984_ = lean_ctor_get(v_b_975_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_b_975_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_b_975_, 0);
lean_dec(v_unused_1019_);
v___x_986_ = v_b_975_;
v_isShared_987_ = v_isSharedCheck_1018_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snd_984_);
lean_dec(v_b_975_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1018_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_988_ = lean_array_uget_borrowed(v_as_972_, v_i_974_);
lean_inc(v_snd_984_);
v___x_989_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8(v_init_970_, v_includeDelayed_971_, v_a_988_, v_snd_984_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1009_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
if (lean_obj_tag(v_a_990_) == 0)
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_a_990_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_994_);
v___x_996_ = v___x_986_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_snd_984_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_996_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_del_object(v___x_992_);
lean_dec(v_snd_984_);
v_a_1001_ = lean_ctor_get(v_a_990_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v_a_990_, 1);
v___x_1002_ = lean_box(0);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_a_1001_);
lean_ctor_set(v___x_986_, 0, v___x_1002_);
v___x_1004_ = v___x_986_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_a_1001_);
v___x_1004_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
size_t v___x_1005_; size_t v___x_1006_; 
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = lean_usize_add(v_i_974_, v___x_1005_);
v_i_974_ = v___x_1006_;
v_b_975_ = v___x_1004_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_del_object(v___x_986_);
lean_dec(v_snd_984_);
v_a_1010_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_989_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_989_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13_spec__15(uint8_t v_includeDelayed_1020_, lean_object* v_as_1021_, size_t v_sz_1022_, size_t v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_usize_dec_lt(v_i_1023_, v_sz_1022_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_b_1024_);
return v___x_1032_;
}
else
{
lean_object* v_snd_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1071_; 
v_snd_1033_ = lean_ctor_get(v_b_1024_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_b_1024_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_b_1024_, 0);
lean_dec(v_unused_1072_);
v___x_1035_ = v_b_1024_;
v_isShared_1036_ = v_isSharedCheck_1071_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_snd_1033_);
lean_dec(v_b_1024_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1071_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v_a_1039_; lean_object* v_a_1046_; 
v___x_1037_ = lean_box(0);
v_a_1046_ = lean_array_uget_borrowed(v_as_1021_, v_i_1023_);
if (lean_obj_tag(v_a_1046_) == 0)
{
v_a_1039_ = v_snd_1033_;
goto v___jp_1038_;
}
else
{
lean_object* v_val_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v_snd_1033_);
v_val_1047_ = lean_ctor_get(v_a_1046_, 0);
v___x_1048_ = l_Lean_LocalDecl_type(v_val_1047_);
v___x_1049_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1048_, v_includeDelayed_1020_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref_known(v___x_1049_, 1);
v___x_1050_ = lean_box(0);
v___x_1051_ = 0;
v___x_1052_ = l_Lean_LocalDecl_value_x3f(v_val_1047_, v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 1)
{
lean_object* v_val_1053_; lean_object* v___x_1054_; 
v_val_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_val_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1053_, v_includeDelayed_1020_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_dec_ref_known(v___x_1054_, 1);
v_a_1039_ = v___x_1050_;
goto v___jp_1038_;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_del_object(v___x_1035_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_dec(v___x_1052_);
v_a_1039_ = v___x_1050_;
goto v___jp_1038_;
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_del_object(v___x_1035_);
v_a_1063_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1049_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1049_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
v___jp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v_a_1039_);
lean_ctor_set(v___x_1035_, 0, v___x_1037_);
v___x_1041_ = v___x_1035_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1039_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
size_t v___x_1042_; size_t v___x_1043_; 
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_add(v_i_1023_, v___x_1042_);
v_i_1023_ = v___x_1043_;
v_b_1024_ = v___x_1041_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13(uint8_t v_includeDelayed_1073_, lean_object* v_as_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_b_1077_);
return v___x_1085_;
}
else
{
lean_object* v_snd_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1124_; 
v_snd_1086_ = lean_ctor_get(v_b_1077_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_b_1077_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_b_1077_, 0);
lean_dec(v_unused_1125_);
v___x_1088_ = v_b_1077_;
v_isShared_1089_ = v_isSharedCheck_1124_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1086_);
lean_dec(v_b_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1124_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v_a_1092_; lean_object* v_a_1099_; 
v___x_1090_ = lean_box(0);
v_a_1099_ = lean_array_uget_borrowed(v_as_1074_, v_i_1076_);
if (lean_obj_tag(v_a_1099_) == 0)
{
v_a_1092_ = v_snd_1086_;
goto v___jp_1091_;
}
else
{
lean_object* v_val_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v_snd_1086_);
v_val_1100_ = lean_ctor_get(v_a_1099_, 0);
v___x_1101_ = l_Lean_LocalDecl_type(v_val_1100_);
v___x_1102_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1101_, v_includeDelayed_1073_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref_known(v___x_1102_, 1);
v___x_1103_ = lean_box(0);
v___x_1104_ = 0;
v___x_1105_ = l_Lean_LocalDecl_value_x3f(v_val_1100_, v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 1)
{
lean_object* v_val_1106_; lean_object* v___x_1107_; 
v_val_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_val_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1106_, v_includeDelayed_1073_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_dec_ref_known(v___x_1107_, 1);
v_a_1092_ = v___x_1103_;
goto v___jp_1091_;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_del_object(v___x_1088_);
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_dec(v___x_1105_);
v_a_1092_ = v___x_1103_;
goto v___jp_1091_;
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_del_object(v___x_1088_);
v_a_1116_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1102_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1102_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
v___jp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v_a_1092_);
lean_ctor_set(v___x_1088_, 0, v___x_1090_);
v___x_1094_ = v___x_1088_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_a_1092_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
size_t v___x_1095_; size_t v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = lean_usize_add(v_i_1076_, v___x_1095_);
v___x_1097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13_spec__15(v_includeDelayed_1073_, v_as_1074_, v_sz_1075_, v___x_1096_, v___x_1094_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8(lean_object* v_init_1126_, uint8_t v_includeDelayed_1127_, lean_object* v_n_1128_, lean_object* v_b_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
if (lean_obj_tag(v_n_1128_) == 0)
{
lean_object* v_cs_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; size_t v_sz_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v_cs_1136_ = lean_ctor_get(v_n_1128_, 0);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v_b_1129_);
v_sz_1139_ = lean_array_size(v_cs_1136_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__12(v_init_1126_, v_includeDelayed_1127_, v_cs_1136_, v_sz_1139_, v___x_1140_, v___x_1138_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1156_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1156_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1156_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_fst_1146_; 
v_fst_1146_ = lean_ctor_get(v_a_1142_, 0);
if (lean_obj_tag(v_fst_1146_) == 0)
{
lean_object* v_snd_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v_snd_1147_ = lean_ctor_get(v_a_1142_, 1);
lean_inc(v_snd_1147_);
lean_dec(v_a_1142_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_snd_1147_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1148_);
v___x_1150_ = v___x_1144_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v_val_1152_; lean_object* v___x_1154_; 
lean_inc_ref(v_fst_1146_);
lean_dec(v_a_1142_);
v_val_1152_ = lean_ctor_get(v_fst_1146_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v_fst_1146_, 1);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_val_1152_);
v___x_1154_ = v___x_1144_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_val_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1141_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1141_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_vs_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; size_t v_sz_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
v_vs_1165_ = lean_ctor_get(v_n_1128_, 0);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v_b_1129_);
v_sz_1168_ = lean_array_size(v_vs_1165_);
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13(v_includeDelayed_1127_, v_vs_1165_, v_sz_1168_, v___x_1169_, v___x_1167_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1185_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1185_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1185_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_fst_1175_; 
v_fst_1175_ = lean_ctor_get(v_a_1171_, 0);
if (lean_obj_tag(v_fst_1175_) == 0)
{
lean_object* v_snd_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v_snd_1176_ = lean_ctor_get(v_a_1171_, 1);
lean_inc(v_snd_1176_);
lean_dec(v_a_1171_);
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_snd_1176_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1177_);
v___x_1179_ = v___x_1173_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
else
{
lean_object* v_val_1181_; lean_object* v___x_1183_; 
lean_inc_ref(v_fst_1175_);
lean_dec(v_a_1171_);
v_val_1181_ = lean_ctor_get(v_fst_1175_, 0);
lean_inc(v_val_1181_);
lean_dec_ref_known(v_fst_1175_, 1);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_val_1181_);
v___x_1183_ = v___x_1173_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_val_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1170_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1170_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9_spec__15(uint8_t v_includeDelayed_1194_, lean_object* v_as_1195_, size_t v_sz_1196_, size_t v_i_1197_, lean_object* v_b_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_usize_dec_lt(v_i_1197_, v_sz_1196_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_b_1198_);
return v___x_1206_;
}
else
{
lean_object* v_snd_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1245_; 
v_snd_1207_ = lean_ctor_get(v_b_1198_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_b_1198_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_b_1198_, 0);
lean_dec(v_unused_1246_);
v___x_1209_ = v_b_1198_;
v_isShared_1210_ = v_isSharedCheck_1245_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_snd_1207_);
lean_dec(v_b_1198_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1245_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v_a_1213_; lean_object* v_a_1220_; 
v___x_1211_ = lean_box(0);
v_a_1220_ = lean_array_uget_borrowed(v_as_1195_, v_i_1197_);
if (lean_obj_tag(v_a_1220_) == 0)
{
v_a_1213_ = v_snd_1207_;
goto v___jp_1212_;
}
else
{
lean_object* v_val_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec(v_snd_1207_);
v_val_1221_ = lean_ctor_get(v_a_1220_, 0);
v___x_1222_ = l_Lean_LocalDecl_type(v_val_1221_);
v___x_1223_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1222_, v_includeDelayed_1194_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref_known(v___x_1223_, 1);
v___x_1224_ = lean_box(0);
v___x_1225_ = 0;
v___x_1226_ = l_Lean_LocalDecl_value_x3f(v_val_1221_, v___x_1225_);
if (lean_obj_tag(v___x_1226_) == 1)
{
lean_object* v_val_1227_; lean_object* v___x_1228_; 
v_val_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1228_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1227_, v_includeDelayed_1194_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_dec_ref_known(v___x_1228_, 1);
v_a_1213_ = v___x_1224_;
goto v___jp_1212_;
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_del_object(v___x_1209_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_dec(v___x_1226_);
v_a_1213_ = v___x_1224_;
goto v___jp_1212_;
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_del_object(v___x_1209_);
v_a_1237_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1223_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1223_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
v___jp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v_a_1213_);
lean_ctor_set(v___x_1209_, 0, v___x_1211_);
v___x_1215_ = v___x_1209_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_a_1213_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
size_t v___x_1216_; size_t v___x_1217_; 
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_add(v_i_1197_, v___x_1216_);
v_i_1197_ = v___x_1217_;
v_b_1198_ = v___x_1215_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9(uint8_t v_includeDelayed_1247_, lean_object* v_as_1248_, size_t v_sz_1249_, size_t v_i_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_usize_dec_lt(v_i_1250_, v_sz_1249_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_b_1251_);
return v___x_1259_;
}
else
{
lean_object* v_snd_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1298_; 
v_snd_1260_ = lean_ctor_get(v_b_1251_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_b_1251_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_b_1251_, 0);
lean_dec(v_unused_1299_);
v___x_1262_ = v_b_1251_;
v_isShared_1263_ = v_isSharedCheck_1298_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snd_1260_);
lean_dec(v_b_1251_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1298_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v_a_1266_; lean_object* v_a_1273_; 
v___x_1264_ = lean_box(0);
v_a_1273_ = lean_array_uget_borrowed(v_as_1248_, v_i_1250_);
if (lean_obj_tag(v_a_1273_) == 0)
{
v_a_1266_ = v_snd_1260_;
goto v___jp_1265_;
}
else
{
lean_object* v_val_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec(v_snd_1260_);
v_val_1274_ = lean_ctor_get(v_a_1273_, 0);
v___x_1275_ = l_Lean_LocalDecl_type(v_val_1274_);
v___x_1276_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1275_, v_includeDelayed_1247_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref_known(v___x_1276_, 1);
v___x_1277_ = lean_box(0);
v___x_1278_ = 0;
v___x_1279_ = l_Lean_LocalDecl_value_x3f(v_val_1274_, v___x_1278_);
if (lean_obj_tag(v___x_1279_) == 1)
{
lean_object* v_val_1280_; lean_object* v___x_1281_; 
v_val_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1280_, v_includeDelayed_1247_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_dec_ref_known(v___x_1281_, 1);
v_a_1266_ = v___x_1277_;
goto v___jp_1265_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_del_object(v___x_1262_);
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
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
else
{
lean_dec(v___x_1279_);
v_a_1266_ = v___x_1277_;
goto v___jp_1265_;
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_del_object(v___x_1262_);
v_a_1290_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1276_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1276_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
v___jp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v_a_1266_);
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1268_ = v___x_1262_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1266_);
v___x_1268_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((size_t)1ULL);
v___x_1270_ = lean_usize_add(v_i_1250_, v___x_1269_);
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9_spec__15(v_includeDelayed_1247_, v_as_1248_, v_sz_1249_, v___x_1270_, v___x_1268_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(uint8_t v_includeDelayed_1300_, lean_object* v_t_1301_, lean_object* v_init_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_root_1309_; lean_object* v_tail_1310_; lean_object* v___x_1311_; 
v_root_1309_ = lean_ctor_get(v_t_1301_, 0);
v_tail_1310_ = lean_ctor_get(v_t_1301_, 1);
v___x_1311_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8(v_init_1302_, v_includeDelayed_1300_, v_root_1309_, v_init_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1348_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1348_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1348_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
if (lean_obj_tag(v_a_1312_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v_a_1312_, 1);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v_a_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; size_t v_sz_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
lean_del_object(v___x_1314_);
v_a_1320_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v_a_1312_, 1);
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v_a_1320_);
v_sz_1323_ = lean_array_size(v_tail_1310_);
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9(v_includeDelayed_1300_, v_tail_1310_, v_sz_1323_, v___x_1324_, v___x_1322_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1339_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1339_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1339_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_fst_1330_; 
v_fst_1330_ = lean_ctor_get(v_a_1326_, 0);
if (lean_obj_tag(v_fst_1330_) == 0)
{
lean_object* v_snd_1331_; lean_object* v___x_1333_; 
v_snd_1331_ = lean_ctor_get(v_a_1326_, 1);
lean_inc(v_snd_1331_);
lean_dec(v_a_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_snd_1331_);
v___x_1333_ = v___x_1328_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_snd_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_object* v_val_1335_; lean_object* v___x_1337_; 
lean_inc_ref(v_fst_1330_);
lean_dec(v_a_1326_);
v_val_1335_ = lean_ctor_get(v_fst_1330_, 0);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_fst_1330_, 1);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_val_1335_);
v___x_1337_ = v___x_1328_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_val_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1325_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1325_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1311_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1311_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object* v_mvarId_1357_, uint8_t v_includeDelayed_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v_i_1377_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v_i_1401_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v_fileName_1451_; lean_object* v_fileMap_1452_; lean_object* v_options_1453_; lean_object* v_currRecDepth_1454_; lean_object* v_maxRecDepth_1455_; lean_object* v_ref_1456_; lean_object* v_currNamespace_1457_; lean_object* v_openDecls_1458_; lean_object* v_initHeartbeats_1459_; lean_object* v_maxHeartbeats_1460_; lean_object* v_quotContext_1461_; lean_object* v_currMacroScope_1462_; uint8_t v_diag_1463_; lean_object* v_cancelTk_x3f_1464_; uint8_t v_suppressElabErrors_1465_; lean_object* v_inheritedTraceOptions_1466_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v_fileName_1451_ = lean_ctor_get(v_a_1362_, 0);
lean_inc_ref(v_fileName_1451_);
v_fileMap_1452_ = lean_ctor_get(v_a_1362_, 1);
lean_inc_ref(v_fileMap_1452_);
v_options_1453_ = lean_ctor_get(v_a_1362_, 2);
lean_inc_ref(v_options_1453_);
v_currRecDepth_1454_ = lean_ctor_get(v_a_1362_, 3);
lean_inc(v_currRecDepth_1454_);
v_maxRecDepth_1455_ = lean_ctor_get(v_a_1362_, 4);
lean_inc(v_maxRecDepth_1455_);
v_ref_1456_ = lean_ctor_get(v_a_1362_, 5);
lean_inc(v_ref_1456_);
v_currNamespace_1457_ = lean_ctor_get(v_a_1362_, 6);
lean_inc(v_currNamespace_1457_);
v_openDecls_1458_ = lean_ctor_get(v_a_1362_, 7);
lean_inc(v_openDecls_1458_);
v_initHeartbeats_1459_ = lean_ctor_get(v_a_1362_, 8);
lean_inc(v_initHeartbeats_1459_);
v_maxHeartbeats_1460_ = lean_ctor_get(v_a_1362_, 9);
lean_inc(v_maxHeartbeats_1460_);
v_quotContext_1461_ = lean_ctor_get(v_a_1362_, 10);
lean_inc(v_quotContext_1461_);
v_currMacroScope_1462_ = lean_ctor_get(v_a_1362_, 11);
lean_inc(v_currMacroScope_1462_);
v_diag_1463_ = lean_ctor_get_uint8(v_a_1362_, sizeof(void*)*14);
v_cancelTk_x3f_1464_ = lean_ctor_get(v_a_1362_, 12);
lean_inc(v_cancelTk_x3f_1464_);
v_suppressElabErrors_1465_ = lean_ctor_get_uint8(v_a_1362_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1466_ = lean_ctor_get(v_a_1362_, 13);
lean_inc_ref(v_inheritedTraceOptions_1466_);
lean_dec_ref(v_a_1362_);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_nat_dec_eq(v_maxRecDepth_1455_, v___x_1521_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_nat_dec_eq(v_currRecDepth_1454_, v_maxRecDepth_1455_);
if (v___x_1523_ == 0)
{
goto v___jp_1467_;
}
else
{
lean_object* v___x_1524_; 
lean_dec_ref(v_inheritedTraceOptions_1466_);
lean_dec(v_cancelTk_x3f_1464_);
lean_dec(v_currMacroScope_1462_);
lean_dec(v_quotContext_1461_);
lean_dec(v_maxHeartbeats_1460_);
lean_dec(v_initHeartbeats_1459_);
lean_dec(v_openDecls_1458_);
lean_dec(v_currNamespace_1457_);
lean_dec(v_maxRecDepth_1455_);
lean_dec(v_currRecDepth_1454_);
lean_dec_ref(v_options_1453_);
lean_dec_ref(v_fileMap_1452_);
lean_dec_ref(v_fileName_1451_);
lean_dec(v_mvarId_1357_);
v___x_1524_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg(v_ref_1456_);
return v___x_1524_;
}
}
else
{
goto v___jp_1467_;
}
v___jp_1365_:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_st_ref_put(v_a_1359_, v___y_1368_);
v_mvarId_1357_ = v___y_1367_;
v_a_1362_ = v___y_1366_;
goto _start;
}
v___jp_1371_:
{
lean_object* v_size_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_size_1378_ = lean_ctor_get(v___y_1376_, 0);
v___x_1379_ = lean_nat_add(v_size_1378_, v___y_1375_);
lean_inc(v___y_1374_);
v___x_1380_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1376_, v___x_1379_, v_i_1377_, v___y_1374_, v___y_1372_);
lean_dec(v_i_1377_);
v___y_1366_ = v___y_1373_;
v___y_1367_ = v___y_1374_;
v___y_1368_ = v___x_1380_;
goto v___jp_1365_;
}
v___jp_1381_:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___y_1386_, v___y_1384_);
switch(lean_obj_tag(v___x_1387_))
{
case 0:
{
lean_object* v_index_1388_; lean_object* v_size_1389_; lean_object* v___x_1390_; 
v_index_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_index_1388_);
lean_dec_ref_known(v___x_1387_, 3);
v_size_1389_ = lean_ctor_get(v___y_1386_, 0);
lean_inc(v_size_1389_);
lean_inc(v___y_1384_);
v___x_1390_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1386_, v_size_1389_, v_index_1388_, v___y_1384_, v___y_1382_);
lean_dec(v_index_1388_);
v___y_1366_ = v___y_1383_;
v___y_1367_ = v___y_1384_;
v___y_1368_ = v___x_1390_;
goto v___jp_1365_;
}
case 1:
{
lean_object* v_index_1391_; 
v_index_1391_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_index_1391_);
lean_dec_ref_known(v___x_1387_, 1);
v___y_1372_ = v___y_1382_;
v___y_1373_ = v___y_1383_;
v___y_1374_ = v___y_1384_;
v___y_1375_ = v___y_1385_;
v___y_1376_ = v___y_1386_;
v_i_1377_ = v_index_1391_;
goto v___jp_1371_;
}
default: 
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1386_, v___x_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_index_1394_; 
v_index_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_index_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___y_1372_ = v___y_1382_;
v___y_1373_ = v___y_1383_;
v___y_1374_ = v___y_1384_;
v___y_1375_ = v___y_1385_;
v___y_1376_ = v___y_1386_;
v_i_1377_ = v_index_1394_;
goto v___jp_1371_;
}
else
{
v___y_1366_ = v___y_1383_;
v___y_1367_ = v___y_1384_;
v___y_1368_ = v___y_1386_;
goto v___jp_1365_;
}
}
}
}
v___jp_1395_:
{
lean_object* v_size_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_size_1402_ = lean_ctor_get(v___y_1396_, 0);
v___x_1403_ = lean_nat_add(v_size_1402_, v___y_1400_);
lean_inc(v___y_1399_);
v___x_1404_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1396_, v___x_1403_, v_i_1401_, v___y_1399_, v___y_1397_);
lean_dec(v_i_1401_);
v___y_1366_ = v___y_1398_;
v___y_1367_ = v___y_1399_;
v___y_1368_ = v___x_1404_;
goto v___jp_1365_;
}
v___jp_1405_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v___y_1410_);
lean_dec_ref(v___y_1410_);
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_1411_, v___y_1408_);
switch(lean_obj_tag(v___x_1412_))
{
case 0:
{
lean_object* v_index_1413_; lean_object* v_size_1414_; lean_object* v___x_1415_; 
v_index_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_index_1413_);
lean_dec_ref_known(v___x_1412_, 3);
v_size_1414_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_size_1414_);
lean_inc(v___y_1408_);
v___x_1415_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1411_, v_size_1414_, v_index_1413_, v___y_1408_, v___y_1406_);
lean_dec(v_index_1413_);
v___y_1366_ = v___y_1407_;
v___y_1367_ = v___y_1408_;
v___y_1368_ = v___x_1415_;
goto v___jp_1365_;
}
case 1:
{
lean_object* v_index_1416_; 
v_index_1416_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_index_1416_);
lean_dec_ref_known(v___x_1412_, 1);
v___y_1396_ = v___x_1411_;
v___y_1397_ = v___y_1406_;
v___y_1398_ = v___y_1407_;
v___y_1399_ = v___y_1408_;
v___y_1400_ = v___y_1409_;
v_i_1401_ = v_index_1416_;
goto v___jp_1395_;
}
default: 
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1411_, v___x_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_index_1419_; 
v_index_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_index_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___y_1396_ = v___x_1411_;
v___y_1397_ = v___y_1406_;
v___y_1398_ = v___y_1407_;
v___y_1399_ = v___y_1408_;
v___y_1400_ = v___y_1409_;
v_i_1401_ = v_index_1419_;
goto v___jp_1395_;
}
else
{
v___y_1366_ = v___y_1407_;
v___y_1367_ = v___y_1408_;
v___y_1368_ = v___x_1411_;
goto v___jp_1365_;
}
}
}
}
v___jp_1420_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_st_ref_take(v_a_1359_);
v___x_1426_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_1425_, v___y_1423_);
switch(lean_obj_tag(v___x_1426_))
{
case 0:
{
lean_dec_ref_known(v___x_1426_, 3);
v___y_1366_ = v___y_1422_;
v___y_1367_ = v___y_1423_;
v___y_1368_ = v___x_1425_;
goto v___jp_1365_;
}
case 1:
{
lean_object* v_index_1427_; lean_object* v_size_1428_; lean_object* v_keyArray_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v_index_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_index_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v_size_1428_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_size_1428_);
v_keyArray_1429_ = lean_ctor_get(v___x_1425_, 1);
lean_inc_ref(v_keyArray_1429_);
v___x_1430_ = lean_nat_add(v_size_1428_, v___y_1424_);
lean_dec(v_size_1428_);
v___x_1431_ = lean_array_get_size(v_keyArray_1429_);
lean_dec_ref(v_keyArray_1429_);
v___x_1432_ = lean_nat_dec_lt(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_dec(v___x_1430_);
lean_dec(v_index_1427_);
v___y_1406_ = v___y_1421_;
v___y_1407_ = v___y_1422_;
v___y_1408_ = v___y_1423_;
v___y_1409_ = v___y_1424_;
v___y_1410_ = v___x_1425_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1433_ = lean_unsigned_to_nat(4u);
v___x_1434_ = lean_nat_mul(v___x_1430_, v___x_1433_);
v___x_1435_ = lean_unsigned_to_nat(3u);
v___x_1436_ = lean_nat_mul(v___x_1431_, v___x_1435_);
v___x_1437_ = lean_nat_dec_le(v___x_1434_, v___x_1436_);
lean_dec(v___x_1436_);
lean_dec(v___x_1434_);
if (v___x_1437_ == 0)
{
lean_dec(v___x_1430_);
lean_dec(v_index_1427_);
v___y_1406_ = v___y_1421_;
v___y_1407_ = v___y_1422_;
v___y_1408_ = v___y_1423_;
v___y_1409_ = v___y_1424_;
v___y_1410_ = v___x_1425_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1438_; 
lean_inc(v___y_1423_);
v___x_1438_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1425_, v___x_1430_, v_index_1427_, v___y_1423_, v___y_1421_);
lean_dec(v_index_1427_);
v___y_1366_ = v___y_1422_;
v___y_1367_ = v___y_1423_;
v___y_1368_ = v___x_1438_;
goto v___jp_1365_;
}
}
}
default: 
{
lean_object* v_size_1439_; lean_object* v_keyArray_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_size_1439_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_size_1439_);
v_keyArray_1440_ = lean_ctor_get(v___x_1425_, 1);
lean_inc_ref(v_keyArray_1440_);
v___x_1441_ = lean_nat_add(v_size_1439_, v___y_1424_);
lean_dec(v_size_1439_);
v___x_1442_ = lean_array_get_size(v_keyArray_1440_);
lean_dec_ref(v_keyArray_1440_);
v___x_1443_ = lean_nat_dec_lt(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_dec(v___x_1441_);
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v___x_1425_);
lean_dec(v___x_1425_);
v___y_1382_ = v___y_1421_;
v___y_1383_ = v___y_1422_;
v___y_1384_ = v___y_1423_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___x_1444_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1445_ = lean_unsigned_to_nat(4u);
v___x_1446_ = lean_nat_mul(v___x_1441_, v___x_1445_);
lean_dec(v___x_1441_);
v___x_1447_ = lean_unsigned_to_nat(3u);
v___x_1448_ = lean_nat_mul(v___x_1442_, v___x_1447_);
v___x_1449_ = lean_nat_dec_le(v___x_1446_, v___x_1448_);
lean_dec(v___x_1448_);
lean_dec(v___x_1446_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v___x_1425_);
lean_dec(v___x_1425_);
v___y_1382_ = v___y_1421_;
v___y_1383_ = v___y_1422_;
v___y_1384_ = v___y_1423_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___x_1450_;
goto v___jp_1381_;
}
else
{
v___y_1382_ = v___y_1421_;
v___y_1383_ = v___y_1422_;
v___y_1384_ = v___y_1423_;
v___y_1385_ = v___y_1424_;
v___y_1386_ = v___x_1425_;
goto v___jp_1381_;
}
}
}
}
}
v___jp_1467_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_nat_add(v_currRecDepth_1454_, v___x_1468_);
lean_dec(v_currRecDepth_1454_);
v___x_1470_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1470_, 0, v_fileName_1451_);
lean_ctor_set(v___x_1470_, 1, v_fileMap_1452_);
lean_ctor_set(v___x_1470_, 2, v_options_1453_);
lean_ctor_set(v___x_1470_, 3, v___x_1469_);
lean_ctor_set(v___x_1470_, 4, v_maxRecDepth_1455_);
lean_ctor_set(v___x_1470_, 5, v_ref_1456_);
lean_ctor_set(v___x_1470_, 6, v_currNamespace_1457_);
lean_ctor_set(v___x_1470_, 7, v_openDecls_1458_);
lean_ctor_set(v___x_1470_, 8, v_initHeartbeats_1459_);
lean_ctor_set(v___x_1470_, 9, v_maxHeartbeats_1460_);
lean_ctor_set(v___x_1470_, 10, v_quotContext_1461_);
lean_ctor_set(v___x_1470_, 11, v_currMacroScope_1462_);
lean_ctor_set(v___x_1470_, 12, v_cancelTk_x3f_1464_);
lean_ctor_set(v___x_1470_, 13, v_inheritedTraceOptions_1466_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*14, v_diag_1463_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*14 + 1, v_suppressElabErrors_1465_);
lean_inc(v_mvarId_1357_);
v___x_1471_ = l_Lean_MVarId_getDecl(v_mvarId_1357_, v_a_1360_, v_a_1361_, v___x_1470_, v_a_1363_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v_lctx_1473_; lean_object* v_type_1474_; lean_object* v___x_1475_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v_lctx_1473_ = lean_ctor_get(v_a_1472_, 1);
lean_inc_ref(v_lctx_1473_);
v_type_1474_ = lean_ctor_get(v_a_1472_, 2);
lean_inc_ref(v_type_1474_);
lean_dec(v_a_1472_);
v___x_1475_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_type_1474_, v_includeDelayed_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1470_, v_a_1363_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_decls_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec_ref_known(v___x_1475_, 1);
v_decls_1476_ = lean_ctor_get(v_lctx_1473_, 1);
lean_inc_ref(v_decls_1476_);
lean_dec_ref(v_lctx_1473_);
v___x_1477_ = lean_box(0);
v___x_1478_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(v_includeDelayed_1358_, v_decls_1476_, v___x_1477_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1470_, v_a_1363_);
lean_dec_ref(v_decls_1476_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref_known(v___x_1478_, 1);
v___x_1479_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_1357_, v_a_1361_);
lean_dec(v_mvarId_1357_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1504_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1504_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1504_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
if (lean_obj_tag(v_a_1480_) == 1)
{
lean_object* v_val_1484_; lean_object* v_mvarIdPending_1485_; lean_object* v___x_1486_; 
lean_del_object(v___x_1482_);
v_val_1484_ = lean_ctor_get(v_a_1480_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v_a_1480_, 1);
v_mvarIdPending_1485_ = lean_ctor_get(v_val_1484_, 1);
lean_inc(v_mvarIdPending_1485_);
lean_dec(v_val_1484_);
v___x_1486_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_mvarIdPending_1485_, v_a_1361_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; uint8_t v___x_1488_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1488_ = lean_unbox(v_a_1487_);
lean_dec(v_a_1487_);
if (v___x_1488_ == 0)
{
v___y_1421_ = v___x_1477_;
v___y_1422_ = v___x_1470_;
v___y_1423_ = v_mvarIdPending_1485_;
v___y_1424_ = v___x_1468_;
goto v___jp_1420_;
}
else
{
v_mvarId_1357_ = v_mvarIdPending_1485_;
v_a_1362_ = v___x_1470_;
goto _start;
}
}
else
{
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1490_; uint8_t v___x_1491_; 
v_a_1490_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1491_ = lean_unbox(v_a_1490_);
lean_dec(v_a_1490_);
if (v___x_1491_ == 0)
{
v_mvarId_1357_ = v_mvarIdPending_1485_;
v_a_1362_ = v___x_1470_;
goto _start;
}
else
{
v___y_1421_ = v___x_1477_;
v___y_1422_ = v___x_1470_;
v___y_1423_ = v_mvarIdPending_1485_;
v___y_1424_ = v___x_1468_;
goto v___jp_1420_;
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v_mvarIdPending_1485_);
lean_dec_ref_known(v___x_1470_, 14);
v_a_1493_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1486_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1486_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
else
{
lean_object* v___x_1502_; 
lean_dec(v_a_1480_);
lean_dec_ref_known(v___x_1470_, 14);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1477_);
v___x_1502_ = v___x_1482_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1477_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref_known(v___x_1470_, 14);
v_a_1505_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1479_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1479_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
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
lean_dec_ref_known(v___x_1470_, 14);
lean_dec(v_mvarId_1357_);
return v___x_1478_;
}
}
else
{
lean_dec_ref(v_lctx_1473_);
lean_dec_ref_known(v___x_1470_, 14);
lean_dec(v_mvarId_1357_);
return v___x_1475_;
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref_known(v___x_1470_, 14);
lean_dec(v_mvarId_1357_);
v_a_1513_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1471_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1471_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__4(lean_object* v_as_1525_, size_t v_i_1526_, size_t v_stop_1527_, lean_object* v_b_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_usize_dec_eq(v_i_1526_, v_stop_1527_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_array_uget_borrowed(v_as_1525_, v_i_1526_);
lean_inc_ref(v___y_1532_);
lean_inc(v___x_1536_);
v___x_1537_ = l___private_Lean_Meta_CollectMVars_0__go(v___x_1536_, v___x_1535_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; size_t v___x_1539_; size_t v___x_1540_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = ((size_t)1ULL);
v___x_1540_ = lean_usize_add(v_i_1526_, v___x_1539_);
v_i_1526_ = v___x_1540_;
v_b_1528_ = v_a_1538_;
goto _start;
}
else
{
return v___x_1537_;
}
}
else
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_b_1528_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__4___boxed(lean_object* v_as_1543_, lean_object* v_i_1544_, lean_object* v_stop_1545_, lean_object* v_b_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
size_t v_i_boxed_1553_; size_t v_stop_boxed_1554_; lean_object* v_res_1555_; 
v_i_boxed_1553_ = lean_unbox_usize(v_i_1544_);
lean_dec(v_i_1544_);
v_stop_boxed_1554_ = lean_unbox_usize(v_stop_1545_);
lean_dec(v_stop_1545_);
v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__4(v_as_1543_, v_i_boxed_1553_, v_stop_boxed_1554_, v_b_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v_as_1543_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__12___boxed(lean_object* v_init_1556_, lean_object* v_includeDelayed_1557_, lean_object* v_as_1558_, lean_object* v_sz_1559_, lean_object* v_i_1560_, lean_object* v_b_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v_includeDelayed_boxed_1568_; size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v_includeDelayed_boxed_1568_ = lean_unbox(v_includeDelayed_1557_);
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1559_);
lean_dec(v_sz_1559_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1560_);
lean_dec(v_i_1560_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__12(v_init_1556_, v_includeDelayed_boxed_1568_, v_as_1558_, v_sz_boxed_1569_, v_i_boxed_1570_, v_b_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v_as_1558_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(lean_object* v_includeDelayed_1572_, lean_object* v_t_1573_, lean_object* v_init_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v_includeDelayed_boxed_1581_; lean_object* v_res_1582_; 
v_includeDelayed_boxed_1581_ = lean_unbox(v_includeDelayed_1572_);
v_res_1582_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(v_includeDelayed_boxed_1581_, v_t_1573_, v_init_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v_t_1573_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9___boxed(lean_object* v_includeDelayed_1583_, lean_object* v_as_1584_, lean_object* v_sz_1585_, lean_object* v_i_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v_includeDelayed_boxed_1594_; size_t v_sz_boxed_1595_; size_t v_i_boxed_1596_; lean_object* v_res_1597_; 
v_includeDelayed_boxed_1594_ = lean_unbox(v_includeDelayed_1583_);
v_sz_boxed_1595_ = lean_unbox_usize(v_sz_1585_);
lean_dec(v_sz_1585_);
v_i_boxed_1596_ = lean_unbox_usize(v_i_1586_);
lean_dec(v_i_1586_);
v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9(v_includeDelayed_boxed_1594_, v_as_1584_, v_sz_boxed_1595_, v_i_boxed_1596_, v_b_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v_as_1584_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13___boxed(lean_object* v_includeDelayed_1598_, lean_object* v_as_1599_, lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v_includeDelayed_boxed_1609_; size_t v_sz_boxed_1610_; size_t v_i_boxed_1611_; lean_object* v_res_1612_; 
v_includeDelayed_boxed_1609_ = lean_unbox(v_includeDelayed_1598_);
v_sz_boxed_1610_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1611_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13(v_includeDelayed_boxed_1609_, v_as_1599_, v_sz_boxed_1610_, v_i_boxed_1611_, v_b_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v_as_1599_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9_spec__15___boxed(lean_object* v_includeDelayed_1613_, lean_object* v_as_1614_, lean_object* v_sz_1615_, lean_object* v_i_1616_, lean_object* v_b_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v_includeDelayed_boxed_1624_; size_t v_sz_boxed_1625_; size_t v_i_boxed_1626_; lean_object* v_res_1627_; 
v_includeDelayed_boxed_1624_ = lean_unbox(v_includeDelayed_1613_);
v_sz_boxed_1625_ = lean_unbox_usize(v_sz_1615_);
lean_dec(v_sz_1615_);
v_i_boxed_1626_ = lean_unbox_usize(v_i_1616_);
lean_dec(v_i_1616_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__9_spec__15(v_includeDelayed_boxed_1624_, v_as_1614_, v_sz_boxed_1625_, v_i_boxed_1626_, v_b_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v_as_1614_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13_spec__15___boxed(lean_object* v_includeDelayed_1628_, lean_object* v_as_1629_, lean_object* v_sz_1630_, lean_object* v_i_1631_, lean_object* v_b_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v_includeDelayed_boxed_1639_; size_t v_sz_boxed_1640_; size_t v_i_boxed_1641_; lean_object* v_res_1642_; 
v_includeDelayed_boxed_1639_ = lean_unbox(v_includeDelayed_1628_);
v_sz_boxed_1640_ = lean_unbox_usize(v_sz_1630_);
lean_dec(v_sz_1630_);
v_i_boxed_1641_ = lean_unbox_usize(v_i_1631_);
lean_dec(v_i_1631_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8_spec__13_spec__15(v_includeDelayed_boxed_1639_, v_as_1629_, v_sz_boxed_1640_, v_i_boxed_1641_, v_b_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v_as_1629_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8___boxed(lean_object* v_init_1643_, lean_object* v_includeDelayed_1644_, lean_object* v_n_1645_, lean_object* v_b_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
uint8_t v_includeDelayed_boxed_1653_; lean_object* v_res_1654_; 
v_includeDelayed_boxed_1653_ = lean_unbox(v_includeDelayed_1644_);
v_res_1654_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_spec__8(v_init_1643_, v_includeDelayed_boxed_1653_, v_n_1645_, v_b_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v_n_1645_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object* v_e_1655_, lean_object* v_includeDelayed_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
uint8_t v_includeDelayed_boxed_1663_; lean_object* v_res_1664_; 
v_includeDelayed_boxed_1663_ = lean_unbox(v_includeDelayed_1656_);
v_res_1664_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1655_, v_includeDelayed_boxed_1663_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go___boxed(lean_object* v_mvarId_1665_, lean_object* v_includeDelayed_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
uint8_t v_includeDelayed_boxed_1673_; lean_object* v_res_1674_; 
v_includeDelayed_boxed_1673_ = lean_unbox(v_includeDelayed_1666_);
v_res_1674_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1665_, v_includeDelayed_boxed_1673_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(lean_object* v_mvarId_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_1675_, v___y_1678_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(lean_object* v_mvarId_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec(v_mvarId_1683_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9(lean_object* v_00_u03b1_1691_, lean_object* v_ref_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___redArg(v_ref_1692_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_ref_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__9(v_00_u03b1_1700_, v_ref_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(lean_object* v_00_u03b2_1709_, lean_object* v_m_1710_, lean_object* v_query_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_1710_, v_query_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___boxed(lean_object* v_00_u03b2_1713_, lean_object* v_m_1714_, lean_object* v_query_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(v_00_u03b2_1713_, v_m_1714_, v_query_1715_);
lean_dec(v_query_1715_);
lean_dec_ref(v_m_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(lean_object* v_00_u03b2_1717_, lean_object* v_m_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_m_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(lean_object* v_00_u03b2_1720_, lean_object* v_m_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_00_u03b2_1720_, v_m_1721_);
lean_dec_ref(v_m_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(lean_object* v_mvarId_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___redArg(v_mvarId_1723_, v___y_1726_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___boxed(lean_object* v_mvarId_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_mvarId_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec(v_mvarId_1731_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_object* v_mvarId_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_mvarId_1739_, v___y_1742_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(lean_object* v_mvarId_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(v_mvarId_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec(v_mvarId_1747_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_query_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_m_1756_, v_query_1757_, v_x_1758_, v_x_1759_, v_x_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1763_, lean_object* v_m_1764_, lean_object* v_query_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_, lean_object* v_x_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(v_00_u03b2_1763_, v_m_1764_, v_query_1765_, v_x_1766_, v_x_1767_, v_x_1768_, v_x_1769_);
lean_dec(v_query_1765_);
lean_dec_ref(v_m_1764_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2(lean_object* v_00_u03b2_1771_, lean_object* v_init_1772_, lean_object* v_b_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___redArg(v_init_1772_, v_b_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1775_, lean_object* v_init_1776_, lean_object* v_b_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2(v_00_u03b2_1775_, v_init_1776_, v_b_1777_);
lean_dec_ref(v_b_1777_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1779_, lean_object* v_b_1780_, lean_object* v_acc_1781_, lean_object* v_i_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___redArg(v_b_1780_, v_acc_1781_, v_i_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1784_, lean_object* v_b_1785_, lean_object* v_acc_1786_, lean_object* v_i_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_spec__2_spec__6(v_00_u03b2_1784_, v_b_1785_, v_acc_1786_, v_i_1787_);
lean_dec_ref(v_b_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies(lean_object* v_mvarId_1789_, uint8_t v_includeDelayed_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1797_ = lean_st_mk_ref(v___x_1796_);
lean_inc_ref(v_a_1793_);
v___x_1798_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1789_, v_includeDelayed_1790_, v___x_1797_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v___x_1798_, 0);
lean_dec(v_unused_1807_);
v___x_1800_ = v___x_1798_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_dec(v___x_1798_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_st_ref_get(v___x_1797_);
lean_dec(v___x_1797_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v___x_1797_);
v_a_1808_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1798_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1798_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object* v_mvarId_1816_, lean_object* v_includeDelayed_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
uint8_t v_includeDelayed_boxed_1823_; lean_object* v_res_1824_; 
v_includeDelayed_boxed_1823_ = lean_unbox(v_includeDelayed_1817_);
v_res_1824_ = l_Lean_MVarId_getMVarDependencies(v_mvarId_1816_, v_includeDelayed_boxed_1823_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies(lean_object* v_e_1825_, uint8_t v_includeDelayed_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1833_ = lean_st_mk_ref(v___x_1832_);
v___x_1834_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1825_, v_includeDelayed_1826_, v___x_1833_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v___x_1834_, 0);
lean_dec(v_unused_1843_);
v___x_1836_ = v___x_1834_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v___x_1834_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = lean_st_ref_get(v___x_1833_);
lean_dec(v___x_1833_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v___x_1833_);
v_a_1844_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1834_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1834_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies___boxed(lean_object* v_e_1852_, lean_object* v_includeDelayed_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
uint8_t v_includeDelayed_boxed_1859_; lean_object* v_res_1860_; 
v_includeDelayed_boxed_1859_ = lean_unbox(v_includeDelayed_1853_);
v_res_1860_ = l_Lean_Expr_getMVarDependencies(v_e_1852_, v_includeDelayed_boxed_1859_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
return v_res_1860_;
}
}
lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CollectMVars(builtin);
}
#ifdef __cplusplus
}
#endif
