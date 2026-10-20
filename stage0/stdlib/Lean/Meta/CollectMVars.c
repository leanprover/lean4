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
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Meta_getMVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_getMVars___closed__2 = (const lean_object*)&l_Lean_Meta_getMVars___closed__2_value;
static lean_once_cell_t l_Lean_Meta_getMVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getMVars___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0;
static lean_once_cell_t l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_81_; lean_object* v___x_82_; lean_object* v_result_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_result_87_; lean_object* v_lower_89_; lean_object* v_upper_90_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v___x_80_, 1);
v___x_82_ = lean_st_ref_get(v_a_74_);
v_result_83_ = lean_ctor_get(v___x_82_, 1);
v___x_84_ = lean_array_get_size(v_result_83_);
v___x_85_ = l_Lean_Expr_collectMVars(v___x_82_, v_a_81_);
lean_inc_ref(v___x_85_);
v___x_86_ = lean_st_ref_swap(v_a_74_, v___x_85_);
lean_dec(v___x_86_);
v_result_87_ = lean_ctor_get(v___x_85_, 1);
lean_inc_ref(v_result_87_);
lean_dec_ref(v___x_85_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_array_get_size(v_result_87_);
v___x_104_ = lean_nat_dec_le(v___x_84_, v___x_102_);
if (v___x_104_ == 0)
{
v_lower_89_ = v___x_84_;
v_upper_90_ = v___x_103_;
goto v___jp_88_;
}
else
{
v_lower_89_ = v___x_102_;
v_upper_90_ = v___x_103_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = l_Array_toSubarray___redArg(v_result_87_, v_lower_89_, v_upper_90_);
v___x_92_ = lean_box(0);
v___x_93_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v___x_91_, v___x_92_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_93_, 0);
lean_dec(v_unused_101_);
v___x_95_ = v___x_93_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_dec(v___x_93_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_92_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_92_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
return v___x_93_;
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
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_129_ = lean_box(0);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_add(v_start_122_, v___x_130_);
lean_inc_ref(v_array_121_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_131_);
v___x_133_ = v___x_125_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_array_121_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v_stop_123_);
v___x_133_ = v_reuseFailAlloc_151_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_array_fget(v_array_121_, v_start_122_);
lean_dec(v_start_122_);
lean_dec_ref(v_array_121_);
v___x_135_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v___x_134_, v___y_117_);
lean_dec(v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
if (lean_obj_tag(v_a_136_) == 0)
{
v_a_113_ = v___x_133_;
v_b_114_ = v___x_129_;
goto _start;
}
else
{
lean_object* v_val_138_; lean_object* v_mvarIdPending_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_val_138_ = lean_ctor_get(v_a_136_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v_a_136_, 1);
v_mvarIdPending_139_ = lean_ctor_get(v_val_138_, 1);
lean_inc(v_mvarIdPending_139_);
lean_dec(v_val_138_);
v___x_140_ = l_Lean_mkMVar(v_mvarIdPending_139_);
v___x_141_ = l_Lean_Meta_collectMVars(v___x_140_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_dec_ref_known(v___x_141_, 1);
v_a_113_ = v___x_133_;
v_b_114_ = v___x_129_;
goto _start;
}
else
{
lean_dec_ref(v___x_133_);
return v___x_141_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref(v___x_133_);
v_a_143_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_135_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_135_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
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
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
v___x_195_ = lean_unsigned_to_nat(16u);
v___x_196_ = lean_mk_array(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__1(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__0, &l_Lean_Meta_getMVars___closed__0_once, _init_l_Lean_Meta_getMVars___closed__0);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_203_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__1, &l_Lean_Meta_getMVars___closed__1_once, _init_l_Lean_Meta_getMVars___closed__1);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars(lean_object* v_e_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_212_ = lean_st_mk_ref(v___x_211_);
v___x_213_ = l_Lean_Meta_collectMVars(v_e_205_, v___x_212_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_222_; 
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v___x_213_, 0);
lean_dec(v_unused_223_);
v___x_215_ = v___x_213_;
v_isShared_216_ = v_isSharedCheck_222_;
goto v_resetjp_214_;
}
else
{
lean_dec(v___x_213_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_222_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v_result_218_; lean_object* v___x_220_; 
v___x_217_ = lean_st_ref_get(v___x_212_);
lean_dec(v___x_212_);
v_result_218_ = lean_ctor_get(v___x_217_, 1);
lean_inc_ref(v_result_218_);
lean_dec(v___x_217_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v_result_218_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_result_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec(v___x_212_);
v_a_224_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_213_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_213_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars___boxed(lean_object* v_e_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Meta_getMVars(v_e_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_239_, lean_object* v_i_240_, lean_object* v_k_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_array_get_size(v_keys_239_);
v___x_243_ = lean_nat_dec_lt(v_i_240_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v_i_240_);
return v___x_243_;
}
else
{
lean_object* v_k_x27_244_; uint8_t v___x_245_; 
v_k_x27_244_ = lean_array_fget_borrowed(v_keys_239_, v_i_240_);
v___x_245_ = l_Lean_instBEqMVarId_beq(v_k_241_, v_k_x27_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_add(v_i_240_, v___x_246_);
lean_dec(v_i_240_);
v_i_240_ = v___x_247_;
goto _start;
}
else
{
lean_dec(v_i_240_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_249_, lean_object* v_i_250_, lean_object* v_k_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_249_, v_i_250_, v_k_251_);
lean_dec(v_k_251_);
lean_dec_ref(v_keys_249_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_254_, size_t v_x_255_, lean_object* v_x_256_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v_es_257_; lean_object* v___x_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v_j_261_; lean_object* v___x_262_; 
v_es_257_ = lean_ctor_get(v_x_254_, 0);
v___x_258_ = lean_box(2);
v___x_259_ = ((size_t)31ULL);
v___x_260_ = lean_usize_land(v_x_255_, v___x_259_);
v_j_261_ = lean_usize_to_nat(v___x_260_);
v___x_262_ = lean_array_get_borrowed(v___x_258_, v_es_257_, v_j_261_);
lean_dec(v_j_261_);
switch(lean_obj_tag(v___x_262_))
{
case 0:
{
lean_object* v_key_263_; uint8_t v___x_264_; 
v_key_263_ = lean_ctor_get(v___x_262_, 0);
v___x_264_ = l_Lean_instBEqMVarId_beq(v_x_256_, v_key_263_);
return v___x_264_;
}
case 1:
{
lean_object* v_node_265_; size_t v___x_266_; size_t v___x_267_; 
v_node_265_ = lean_ctor_get(v___x_262_, 0);
v___x_266_ = ((size_t)5ULL);
v___x_267_ = lean_usize_shift_right(v_x_255_, v___x_266_);
v_x_254_ = v_node_265_;
v_x_255_ = v___x_267_;
goto _start;
}
default: 
{
uint8_t v___x_269_; 
v___x_269_ = 0;
return v___x_269_;
}
}
}
else
{
lean_object* v_ks_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_ks_270_ = lean_ctor_get(v_x_254_, 0);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_270_, v___x_271_, v_x_256_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
size_t v_x_1275__boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_x_1275__boxed_276_ = lean_unbox_usize(v_x_274_);
lean_dec(v_x_274_);
v_res_277_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_273_, v_x_1275__boxed_276_, v_x_275_);
lean_dec(v_x_275_);
lean_dec_ref(v_x_273_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
uint64_t v___x_281_; size_t v___x_282_; uint8_t v___x_283_; 
v___x_281_ = l_Lean_instHashableMVarId_hash(v_x_280_);
v___x_282_ = lean_uint64_to_usize(v___x_281_);
v___x_283_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_279_, v___x_282_, v_x_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg___boxed(lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_284_, v_x_285_);
lean_dec(v_x_285_);
lean_dec_ref(v_x_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(lean_object* v_mvarId_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; lean_object* v_mctx_292_; lean_object* v_dAssignment_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_291_ = lean_st_ref_get(v___y_289_);
v_mctx_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_mctx_292_);
lean_dec(v___x_291_);
v_dAssignment_293_ = lean_ctor_get(v_mctx_292_, 9);
lean_inc_ref(v_dAssignment_293_);
lean_dec_ref(v_mctx_292_);
v___x_294_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_293_, v_mvarId_288_);
lean_dec_ref(v_dAssignment_293_);
v___x_295_ = lean_box(v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(lean_object* v_mvarId_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec(v_mvarId_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(lean_object* v_as_301_, size_t v_i_302_, size_t v_stop_303_, lean_object* v_b_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_a_311_; uint8_t v___x_315_; 
v___x_315_ = lean_usize_dec_eq(v_i_302_, v_stop_303_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_array_uget_borrowed(v_as_301_, v_i_302_);
v___x_317_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v___x_316_, v___y_306_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; uint8_t v___x_319_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v___x_319_ = lean_unbox(v_a_318_);
lean_dec(v_a_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_inc(v___x_316_);
v___x_320_ = lean_array_push(v_b_304_, v___x_316_);
v_a_311_ = v___x_320_;
goto v___jp_310_;
}
else
{
v_a_311_ = v_b_304_;
goto v___jp_310_;
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_b_304_);
v_a_321_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_317_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_317_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_b_304_);
return v___x_329_;
}
v___jp_310_:
{
size_t v___x_312_; size_t v___x_313_; 
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_add(v_i_302_, v___x_312_);
v_i_302_ = v___x_313_;
v_b_304_ = v_a_311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1___boxed(lean_object* v_as_330_, lean_object* v_i_331_, lean_object* v_stop_332_, lean_object* v_b_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
size_t v_i_boxed_339_; size_t v_stop_boxed_340_; lean_object* v_res_341_; 
v_i_boxed_339_ = lean_unbox_usize(v_i_331_);
lean_dec(v_i_331_);
v_stop_boxed_340_ = lean_unbox_usize(v_stop_332_);
lean_dec(v_stop_332_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_330_, v_i_boxed_339_, v_stop_boxed_340_, v_b_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec_ref(v_as_330_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_getMVars(v_e_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_363_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_363_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_363_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_363_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_array_get_size(v_a_349_);
v___x_355_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_356_ = lean_nat_dec_lt(v___x_353_, v___x_354_);
if (v___x_356_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v_a_349_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_355_);
v___x_358_ = v___x_351_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_355_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
else
{
size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; 
lean_del_object(v___x_351_);
v___x_360_ = ((size_t)0ULL);
v___x_361_ = lean_usize_of_nat(v___x_354_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_349_, v___x_360_, v___x_361_, v___x_355_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_349_);
return v___x_362_;
}
}
}
else
{
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object* v_e_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_getMVarsNoDelayed(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(lean_object* v_mvarId_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_371_, v___y_373_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(lean_object* v_mvarId_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(v_mvarId_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v_mvarId_378_);
return v_res_384_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(lean_object* v_00_u03b2_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_386_, v_x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(v_00_u03b2_389_, v_x_390_, v_x_391_);
lean_dec(v_x_391_);
lean_dec_ref(v_x_390_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_394_, lean_object* v_x_395_, size_t v_x_396_, lean_object* v_x_397_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_395_, v_x_396_, v_x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_399_, lean_object* v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
size_t v_x_1460__boxed_403_; uint8_t v_res_404_; lean_object* v_r_405_; 
v_x_1460__boxed_403_ = lean_unbox_usize(v_x_401_);
lean_dec(v_x_401_);
v_res_404_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(v_00_u03b2_399_, v_x_400_, v_x_1460__boxed_403_, v_x_402_);
lean_dec(v_x_402_);
lean_dec_ref(v_x_400_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_406_, lean_object* v_keys_407_, lean_object* v_vals_408_, lean_object* v_heq_409_, lean_object* v_i_410_, lean_object* v_k_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_407_, v_i_410_, v_k_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_413_, lean_object* v_keys_414_, lean_object* v_vals_415_, lean_object* v_heq_416_, lean_object* v_i_417_, lean_object* v_k_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_413_, v_keys_414_, v_vals_415_, v_heq_416_, v_i_417_, v_k_418_);
lean_dec(v_k_418_);
lean_dec_ref(v_vals_415_);
lean_dec_ref(v_keys_414_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(lean_object* v_x_421_, lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_x_421_);
return v___x_429_;
}
else
{
lean_object* v_head_430_; lean_object* v_tail_431_; lean_object* v_type_432_; lean_object* v___x_433_; 
v_head_430_ = lean_ctor_get(v_x_422_, 0);
lean_inc(v_head_430_);
v_tail_431_ = lean_ctor_get(v_x_422_, 1);
lean_inc(v_tail_431_);
lean_dec_ref_known(v_x_422_, 2);
v_type_432_ = lean_ctor_get(v_head_430_, 1);
lean_inc_ref(v_type_432_);
lean_dec(v_head_430_);
v___x_433_ = l_Lean_Meta_collectMVars(v_type_432_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v_x_421_ = v_a_434_;
v_x_422_ = v_tail_431_;
goto _start;
}
else
{
lean_dec(v_tail_431_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_436_, v_x_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v_x_445_);
return v___x_453_;
}
else
{
lean_object* v_head_454_; lean_object* v_tail_455_; lean_object* v_type_456_; lean_object* v_ctors_457_; lean_object* v___x_458_; 
v_head_454_ = lean_ctor_get(v_x_446_, 0);
lean_inc(v_head_454_);
v_tail_455_ = lean_ctor_get(v_x_446_, 1);
lean_inc(v_tail_455_);
lean_dec_ref_known(v_x_446_, 2);
v_type_456_ = lean_ctor_get(v_head_454_, 1);
lean_inc_ref(v_type_456_);
v_ctors_457_ = lean_ctor_get(v_head_454_, 2);
lean_inc(v_ctors_457_);
lean_dec(v_head_454_);
v___x_458_ = l_Lean_Meta_collectMVars(v_type_456_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_a_459_, v_ctors_457_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v_x_445_ = v_a_461_;
v_x_446_ = v_tail_455_;
goto _start;
}
else
{
lean_dec(v_tail_455_);
return v___x_460_;
}
}
else
{
lean_dec(v_ctors_457_);
lean_dec(v_tail_455_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_463_, v_x_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v_x_472_);
return v___x_480_;
}
else
{
lean_object* v_head_481_; lean_object* v_toConstantVal_482_; lean_object* v_tail_483_; lean_object* v_value_484_; lean_object* v_type_485_; lean_object* v___x_486_; 
v_head_481_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_head_481_);
v_toConstantVal_482_ = lean_ctor_get(v_head_481_, 0);
lean_inc_ref(v_toConstantVal_482_);
v_tail_483_ = lean_ctor_get(v_x_473_, 1);
lean_inc(v_tail_483_);
lean_dec_ref_known(v_x_473_, 2);
v_value_484_ = lean_ctor_get(v_head_481_, 1);
lean_inc_ref(v_value_484_);
lean_dec(v_head_481_);
v_type_485_ = lean_ctor_get(v_toConstantVal_482_, 2);
lean_inc_ref(v_type_485_);
lean_dec_ref(v_toConstantVal_482_);
v___x_486_ = l_Lean_Meta_collectMVars(v_type_485_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v___x_487_; 
lean_dec_ref_known(v___x_486_, 1);
v___x_487_ = l_Lean_Meta_collectMVars(v_value_484_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v_x_472_ = v_a_488_;
v_x_473_ = v_tail_483_;
goto _start;
}
else
{
lean_dec(v_tail_483_);
return v___x_487_;
}
}
else
{
lean_dec_ref(v_value_484_);
lean_dec(v_tail_483_);
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_490_, v_x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(lean_object* v_d_499_, lean_object* v_a_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
switch(lean_obj_tag(v_d_499_))
{
case 0:
{
lean_object* v_val_507_; lean_object* v_toConstantVal_508_; lean_object* v_type_509_; lean_object* v___x_510_; 
v_val_507_ = lean_ctor_get(v_d_499_, 0);
lean_inc_ref(v_val_507_);
lean_dec_ref_known(v_d_499_, 1);
v_toConstantVal_508_ = lean_ctor_get(v_val_507_, 0);
lean_inc_ref(v_toConstantVal_508_);
lean_dec_ref(v_val_507_);
v_type_509_ = lean_ctor_get(v_toConstantVal_508_, 2);
lean_inc_ref(v_type_509_);
lean_dec_ref(v_toConstantVal_508_);
v___x_510_ = l_Lean_Meta_collectMVars(v_type_509_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_510_;
}
case 4:
{
lean_object* v___x_511_; 
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_a_500_);
return v___x_511_;
}
case 5:
{
lean_object* v_defns_512_; lean_object* v___x_513_; 
v_defns_512_ = lean_ctor_get(v_d_499_, 0);
lean_inc(v_defns_512_);
lean_dec_ref_known(v_d_499_, 1);
v___x_513_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_a_500_, v_defns_512_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_513_;
}
case 6:
{
lean_object* v_types_514_; lean_object* v___x_515_; 
v_types_514_ = lean_ctor_get(v_d_499_, 2);
lean_inc(v_types_514_);
lean_dec_ref_known(v_d_499_, 3);
v___x_515_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_a_500_, v_types_514_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_515_;
}
default: 
{
lean_object* v_val_516_; lean_object* v_toConstantVal_517_; lean_object* v_value_518_; lean_object* v_type_519_; lean_object* v___x_520_; 
v_val_516_ = lean_ctor_get(v_d_499_, 0);
lean_inc_ref(v_val_516_);
lean_dec(v_d_499_);
v_toConstantVal_517_ = lean_ctor_get(v_val_516_, 0);
lean_inc_ref(v_toConstantVal_517_);
v_value_518_ = lean_ctor_get(v_val_516_, 1);
lean_inc_ref(v_value_518_);
lean_dec_ref(v_val_516_);
v_type_519_ = lean_ctor_get(v_toConstantVal_517_, 2);
lean_inc_ref(v_type_519_);
lean_dec_ref(v_toConstantVal_517_);
v___x_520_ = l_Lean_Meta_collectMVars(v_type_519_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_521_; 
lean_dec_ref_known(v___x_520_, 1);
v___x_521_ = l_Lean_Meta_collectMVars(v_value_518_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_521_;
}
else
{
lean_dec_ref(v_value_518_);
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(lean_object* v_d_522_, lean_object* v_a_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_522_, v_a_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object* v_d_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_box(0);
v___x_539_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_531_, v___x_538_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object* v_d_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Meta_collectMVarsAtDecl(v_d_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object* v_d_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_555_ = lean_st_mk_ref(v___x_554_);
v___x_556_ = l_Lean_Meta_collectMVarsAtDecl(v_d_548_, v___x_555_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_565_; 
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v___x_556_, 0);
lean_dec(v_unused_566_);
v___x_558_ = v___x_556_;
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
else
{
lean_dec(v___x_556_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v_result_561_; lean_object* v___x_563_; 
v___x_560_ = lean_st_ref_get(v___x_555_);
lean_dec(v___x_555_);
v_result_561_ = lean_ctor_get(v___x_560_, 1);
lean_inc_ref(v_result_561_);
lean_dec(v___x_560_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_result_561_);
v___x_563_ = v___x_558_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_result_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v___x_555_);
v_a_567_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_556_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_556_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object* v_d_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Meta_getMVarsAtDecl(v_d_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(lean_object* v_mvarId_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_mctx_586_; lean_object* v_dAssignment_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_585_ = lean_st_ref_get(v___y_583_);
v_mctx_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_mctx_586_);
lean_dec(v___x_585_);
v_dAssignment_587_ = lean_ctor_get(v_mctx_586_, 9);
lean_inc_ref(v_dAssignment_587_);
lean_dec_ref(v_mctx_586_);
v___x_588_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_587_, v_mvarId_582_);
lean_dec_ref(v_dAssignment_587_);
v___x_589_ = lean_box(v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(lean_object* v_mvarId_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec(v_mvarId_591_);
return v_res_594_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(lean_object* v_a_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
uint8_t v___x_597_; 
v___x_597_ = 0;
return v___x_597_;
}
else
{
lean_object* v_key_598_; lean_object* v_tail_599_; uint8_t v___x_600_; 
v_key_598_ = lean_ctor_get(v_x_596_, 0);
v_tail_599_ = lean_ctor_get(v_x_596_, 2);
v___x_600_ = l_Lean_instBEqMVarId_beq(v_key_598_, v_a_595_);
if (v___x_600_ == 0)
{
v_x_596_ = v_tail_599_;
goto _start;
}
else
{
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_602_, lean_object* v_x_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_602_, v_x_603_);
lean_dec(v_x_603_);
lean_dec(v_a_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_x_606_, lean_object* v_x_607_){
_start:
{
if (lean_obj_tag(v_x_607_) == 0)
{
return v_x_606_;
}
else
{
lean_object* v_key_608_; lean_object* v_value_609_; lean_object* v_tail_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_633_; 
v_key_608_ = lean_ctor_get(v_x_607_, 0);
v_value_609_ = lean_ctor_get(v_x_607_, 1);
v_tail_610_ = lean_ctor_get(v_x_607_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_607_);
if (v_isSharedCheck_633_ == 0)
{
v___x_612_ = v_x_607_;
v_isShared_613_ = v_isSharedCheck_633_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_tail_610_);
lean_inc(v_value_609_);
lean_inc(v_key_608_);
lean_dec(v_x_607_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_633_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; uint64_t v___x_615_; uint64_t v___x_616_; uint64_t v___x_617_; uint64_t v_fold_618_; uint64_t v___x_619_; uint64_t v___x_620_; uint64_t v___x_621_; size_t v___x_622_; size_t v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_614_ = lean_array_get_size(v_x_606_);
v___x_615_ = l_Lean_instHashableMVarId_hash(v_key_608_);
v___x_616_ = 32ULL;
v___x_617_ = lean_uint64_shift_right(v___x_615_, v___x_616_);
v_fold_618_ = lean_uint64_xor(v___x_615_, v___x_617_);
v___x_619_ = 16ULL;
v___x_620_ = lean_uint64_shift_right(v_fold_618_, v___x_619_);
v___x_621_ = lean_uint64_xor(v_fold_618_, v___x_620_);
v___x_622_ = lean_uint64_to_usize(v___x_621_);
v___x_623_ = lean_usize_of_nat(v___x_614_);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_sub(v___x_623_, v___x_624_);
v___x_626_ = lean_usize_land(v___x_622_, v___x_625_);
v___x_627_ = lean_array_uget_borrowed(v_x_606_, v___x_626_);
lean_inc(v___x_627_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 2, v___x_627_);
v___x_629_ = v___x_612_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_key_608_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_value_609_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v___x_627_);
v___x_629_ = v_reuseFailAlloc_632_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; 
v___x_630_ = lean_array_uset(v_x_606_, v___x_626_, v___x_629_);
v_x_606_ = v___x_630_;
v_x_607_ = v_tail_610_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(lean_object* v_i_634_, lean_object* v_source_635_, lean_object* v_target_636_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_array_get_size(v_source_635_);
v___x_638_ = lean_nat_dec_lt(v_i_634_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec_ref(v_source_635_);
lean_dec(v_i_634_);
return v_target_636_;
}
else
{
lean_object* v_es_639_; lean_object* v___x_640_; lean_object* v_source_641_; lean_object* v_target_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_es_639_ = lean_array_fget(v_source_635_, v_i_634_);
v___x_640_ = lean_box(0);
v_source_641_ = lean_array_fset(v_source_635_, v_i_634_, v___x_640_);
v_target_642_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_target_636_, v_es_639_);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_i_634_, v___x_643_);
lean_dec(v_i_634_);
v_i_634_ = v___x_644_;
v_source_635_ = v_source_641_;
v_target_636_ = v_target_642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(lean_object* v_data_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_nbuckets_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_647_ = lean_array_get_size(v_data_646_);
v___x_648_ = lean_unsigned_to_nat(2u);
v_nbuckets_649_ = lean_nat_mul(v___x_647_, v___x_648_);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_box(0);
v___x_652_ = lean_mk_array(v_nbuckets_649_, v___x_651_);
v___x_653_ = lean_array_propagate_mark(v_data_646_, v___x_652_);
v___x_654_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v___x_650_, v_data_646_, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(lean_object* v_m_655_, lean_object* v_a_656_, lean_object* v_b_657_){
_start:
{
lean_object* v_size_658_; lean_object* v_buckets_659_; lean_object* v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v_fold_664_; uint64_t v___x_665_; uint64_t v___x_666_; uint64_t v___x_667_; size_t v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; lean_object* v_bkt_673_; uint8_t v___x_674_; 
v_size_658_ = lean_ctor_get(v_m_655_, 0);
v_buckets_659_ = lean_ctor_get(v_m_655_, 1);
v___x_660_ = lean_array_get_size(v_buckets_659_);
v___x_661_ = l_Lean_instHashableMVarId_hash(v_a_656_);
v___x_662_ = 32ULL;
v___x_663_ = lean_uint64_shift_right(v___x_661_, v___x_662_);
v_fold_664_ = lean_uint64_xor(v___x_661_, v___x_663_);
v___x_665_ = 16ULL;
v___x_666_ = lean_uint64_shift_right(v_fold_664_, v___x_665_);
v___x_667_ = lean_uint64_xor(v_fold_664_, v___x_666_);
v___x_668_ = lean_uint64_to_usize(v___x_667_);
v___x_669_ = lean_usize_of_nat(v___x_660_);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_sub(v___x_669_, v___x_670_);
v___x_672_ = lean_usize_land(v___x_668_, v___x_671_);
v_bkt_673_ = lean_array_uget_borrowed(v_buckets_659_, v___x_672_);
v___x_674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_656_, v_bkt_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_695_; 
lean_inc_ref(v_buckets_659_);
lean_inc(v_size_658_);
v_isSharedCheck_695_ = !lean_is_exclusive(v_m_655_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; 
v_unused_696_ = lean_ctor_get(v_m_655_, 1);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_m_655_, 0);
lean_dec(v_unused_697_);
v___x_676_ = v_m_655_;
v_isShared_677_ = v_isSharedCheck_695_;
goto v_resetjp_675_;
}
else
{
lean_dec(v_m_655_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_695_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v_size_x27_679_; lean_object* v___x_680_; lean_object* v_buckets_x27_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_678_ = lean_unsigned_to_nat(1u);
v_size_x27_679_ = lean_nat_add(v_size_658_, v___x_678_);
lean_dec(v_size_658_);
lean_inc(v_bkt_673_);
v___x_680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_680_, 0, v_a_656_);
lean_ctor_set(v___x_680_, 1, v_b_657_);
lean_ctor_set(v___x_680_, 2, v_bkt_673_);
v_buckets_x27_681_ = lean_array_uset(v_buckets_659_, v___x_672_, v___x_680_);
v___x_682_ = lean_unsigned_to_nat(4u);
v___x_683_ = lean_nat_mul(v_size_x27_679_, v___x_682_);
v___x_684_ = lean_unsigned_to_nat(3u);
v___x_685_ = lean_nat_div(v___x_683_, v___x_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_array_get_size(v_buckets_x27_681_);
v___x_687_ = lean_nat_dec_le(v___x_685_, v___x_686_);
lean_dec(v___x_685_);
if (v___x_687_ == 0)
{
lean_object* v_val_688_; lean_object* v___x_690_; 
v_val_688_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_buckets_x27_681_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v_val_688_);
lean_ctor_set(v___x_676_, 0, v_size_x27_679_);
v___x_690_ = v___x_676_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_size_x27_679_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_val_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
else
{
lean_object* v___x_693_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v_buckets_x27_681_);
lean_ctor_set(v___x_676_, 0, v_size_x27_679_);
v___x_693_ = v___x_676_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_size_x27_679_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_buckets_x27_681_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_dec(v_b_657_);
lean_dec(v_a_656_);
return v_m_655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(uint8_t v_includeDelayed_698_, lean_object* v_as_699_, size_t v_sz_700_, size_t v_i_701_, lean_object* v_b_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_a_710_; uint8_t v___x_714_; 
v___x_714_ = lean_usize_dec_lt(v_i_701_, v_sz_700_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_b_702_);
return v___x_715_;
}
else
{
lean_object* v_a_716_; 
v_a_716_ = lean_array_uget_borrowed(v_as_699_, v_i_701_);
if (v_includeDelayed_698_ == 0)
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_a_716_, v___y_705_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; uint8_t v___x_722_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_unbox(v_a_721_);
lean_dec(v_a_721_);
if (v___x_722_ == 0)
{
goto v___jp_717_;
}
else
{
v_a_710_ = v_b_702_;
goto v___jp_709_;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_b_702_);
v_a_723_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_720_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_720_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
goto v___jp_717_;
}
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_box(0);
lean_inc(v_a_716_);
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_b_702_, v_a_716_, v___x_718_);
v_a_710_ = v___x_719_;
goto v___jp_709_;
}
}
v___jp_709_:
{
size_t v___x_711_; size_t v___x_712_; 
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_add(v_i_701_, v___x_711_);
v_i_701_ = v___x_712_;
v_b_702_ = v_a_710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___boxed(lean_object* v_includeDelayed_731_, lean_object* v_as_732_, lean_object* v_sz_733_, lean_object* v_i_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
uint8_t v_includeDelayed_boxed_742_; size_t v_sz_boxed_743_; size_t v_i_boxed_744_; lean_object* v_res_745_; 
v_includeDelayed_boxed_742_ = lean_unbox(v_includeDelayed_731_);
v_sz_boxed_743_ = lean_unbox_usize(v_sz_733_);
lean_dec(v_sz_733_);
v_i_boxed_744_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_boxed_742_, v_as_732_, v_sz_boxed_743_, v_i_boxed_744_, v_b_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v_as_732_);
return v_res_745_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = l_Lean_maxRecDepthErrorMessage;
v___x_752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3);
v___x_754_ = l_Lean_MessageData_ofFormat(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4);
v___x_756_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2));
v___x_757_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(lean_object* v_ref_758_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_ref_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(lean_object* v_ref_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_763_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(lean_object* v_mvarId_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v_mctx_770_; lean_object* v_eAssignment_771_; lean_object* v_dAssignment_772_; uint8_t v___x_773_; 
v___x_769_ = lean_st_ref_get(v___y_767_);
v_mctx_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_ref(v_mctx_770_);
lean_dec(v___x_769_);
v_eAssignment_771_ = lean_ctor_get(v_mctx_770_, 8);
lean_inc_ref(v_eAssignment_771_);
v_dAssignment_772_ = lean_ctor_get(v_mctx_770_, 9);
lean_inc_ref(v_dAssignment_772_);
lean_dec_ref(v_mctx_770_);
v___x_773_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_eAssignment_771_, v_mvarId_766_);
lean_dec_ref(v_eAssignment_771_);
if (v___x_773_ == 0)
{
uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_772_, v_mvarId_766_);
lean_dec_ref(v_dAssignment_772_);
v___x_775_ = lean_box(v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v_dAssignment_772_);
v___x_777_ = lean_box(v___x_773_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(lean_object* v_mvarId_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec(v_mvarId_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(lean_object* v_mvarId_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; lean_object* v_mctx_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_786_ = lean_st_ref_get(v___y_784_);
v_mctx_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref(v_mctx_787_);
lean_dec(v___x_786_);
v___x_788_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_787_, v_mvarId_783_);
lean_dec_ref(v_mctx_787_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg___boxed(lean_object* v_mvarId_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec(v_mvarId_790_);
return v_res_793_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = lean_box(0);
v___x_795_ = lean_unsigned_to_nat(16u);
v___x_796_ = lean_mk_array(v___x_795_, v___x_794_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v___x_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars(lean_object* v_e_800_, uint8_t v_includeDelayed_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_getMVars(v_e_800_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; size_t v_sz_814_; size_t v___x_815_; lean_object* v___x_816_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v___x_810_ = lean_st_ref_get(v_a_802_);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_813_ = lean_st_ref_swap(v_a_802_, v___x_812_);
lean_dec(v___x_813_);
v_sz_814_ = lean_array_size(v_a_809_);
v___x_815_ = ((size_t)0ULL);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_801_, v_a_809_, v_sz_814_, v___x_815_, v___x_810_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_830_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_830_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_830_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_830_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_821_ = lean_st_ref_swap(v_a_802_, v_a_817_);
lean_dec(v___x_821_);
v___x_822_ = lean_array_get_size(v_a_809_);
v___x_823_ = lean_box(0);
v___x_824_ = lean_nat_dec_lt(v___x_811_, v___x_822_);
if (v___x_824_ == 0)
{
lean_object* v___x_826_; 
lean_dec(v_a_809_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_823_);
v___x_826_ = v___x_819_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_823_);
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
size_t v___x_828_; lean_object* v___x_829_; 
lean_del_object(v___x_819_);
v___x_828_ = lean_usize_of_nat(v___x_822_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_809_, v___x_815_, v___x_828_, v___x_823_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_809_);
return v___x_829_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_a_809_);
v_a_831_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_816_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_816_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_808_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_808_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(lean_object* v_init_847_, uint8_t v_includeDelayed_848_, lean_object* v_as_849_, size_t v_sz_850_, size_t v_i_851_, lean_object* v_b_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v_b_852_);
return v___x_860_;
}
else
{
lean_object* v_snd_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_895_; 
v_snd_861_ = lean_ctor_get(v_b_852_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_b_852_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_b_852_, 0);
lean_dec(v_unused_896_);
v___x_863_ = v_b_852_;
v_isShared_864_ = v_isSharedCheck_895_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_snd_861_);
lean_dec(v_b_852_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_895_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v_a_866_; lean_object* v___x_867_; 
v___x_865_ = lean_box(0);
v_a_866_ = lean_array_uget_borrowed(v_as_849_, v_i_851_);
lean_inc(v_snd_861_);
v___x_867_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_847_, v_includeDelayed_848_, v_a_866_, v_snd_861_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_886_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_886_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_886_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_886_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
if (lean_obj_tag(v_a_868_) == 0)
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v_a_868_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_872_);
v___x_874_ = v___x_863_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_snd_861_);
v___x_874_ = v_reuseFailAlloc_878_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_874_);
v___x_876_ = v___x_870_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; 
lean_del_object(v___x_870_);
lean_dec(v_snd_861_);
v_a_879_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v_a_868_, 1);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_a_879_);
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_881_ = v___x_863_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_a_879_);
v___x_881_ = v_reuseFailAlloc_885_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
size_t v___x_882_; size_t v___x_883_; 
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_add(v_i_851_, v___x_882_);
v_i_851_ = v___x_883_;
v_b_852_ = v___x_881_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_del_object(v___x_863_);
lean_dec(v_snd_861_);
v_a_887_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_867_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_867_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(uint8_t v_includeDelayed_897_, lean_object* v_as_898_, size_t v_sz_899_, size_t v_i_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = lean_usize_dec_lt(v_i_900_, v_sz_899_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v_b_901_);
return v___x_909_;
}
else
{
lean_object* v_snd_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_948_; 
v_snd_910_ = lean_ctor_get(v_b_901_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_b_901_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_b_901_, 0);
lean_dec(v_unused_949_);
v___x_912_ = v_b_901_;
v_isShared_913_ = v_isSharedCheck_948_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_snd_910_);
lean_dec(v_b_901_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_948_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v_a_916_; lean_object* v_a_923_; 
v___x_914_ = lean_box(0);
v_a_923_ = lean_array_uget_borrowed(v_as_898_, v_i_900_);
if (lean_obj_tag(v_a_923_) == 0)
{
v_a_916_ = v_snd_910_;
goto v___jp_915_;
}
else
{
lean_object* v_val_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_snd_910_);
v_val_924_ = lean_ctor_get(v_a_923_, 0);
v___x_925_ = lean_box(0);
v___x_926_ = l_Lean_LocalDecl_type(v_val_924_);
v___x_927_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_926_, v_includeDelayed_897_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_927_) == 0)
{
uint8_t v___x_928_; lean_object* v___x_929_; 
lean_dec_ref_known(v___x_927_, 1);
v___x_928_ = 0;
v___x_929_ = l_Lean_LocalDecl_value_x3f(v_val_924_, v___x_928_);
if (lean_obj_tag(v___x_929_) == 1)
{
lean_object* v_val_930_; lean_object* v___x_931_; 
v_val_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_930_, v_includeDelayed_897_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_dec_ref_known(v___x_931_, 1);
v_a_916_ = v___x_925_;
goto v___jp_915_;
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_del_object(v___x_912_);
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_dec(v___x_929_);
v_a_916_ = v___x_925_;
goto v___jp_915_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_del_object(v___x_912_);
v_a_940_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_927_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_927_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
v___jp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_a_916_);
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_918_ = v___x_912_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_a_916_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
size_t v___x_919_; size_t v___x_920_; 
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_900_, v___x_919_);
v_i_900_ = v___x_920_;
v_b_901_ = v___x_918_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(uint8_t v_includeDelayed_950_, lean_object* v_as_951_, size_t v_sz_952_, size_t v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = lean_usize_dec_lt(v_i_953_, v_sz_952_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_b_954_);
return v___x_962_;
}
else
{
lean_object* v_snd_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1001_; 
v_snd_963_ = lean_ctor_get(v_b_954_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_b_954_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; 
v_unused_1002_ = lean_ctor_get(v_b_954_, 0);
lean_dec(v_unused_1002_);
v___x_965_ = v_b_954_;
v_isShared_966_ = v_isSharedCheck_1001_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_snd_963_);
lean_dec(v_b_954_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1001_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v_a_969_; lean_object* v_a_976_; 
v___x_967_ = lean_box(0);
v_a_976_ = lean_array_uget_borrowed(v_as_951_, v_i_953_);
if (lean_obj_tag(v_a_976_) == 0)
{
v_a_969_ = v_snd_963_;
goto v___jp_968_;
}
else
{
lean_object* v_val_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec(v_snd_963_);
v_val_977_ = lean_ctor_get(v_a_976_, 0);
v___x_978_ = lean_box(0);
v___x_979_ = l_Lean_LocalDecl_type(v_val_977_);
v___x_980_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_979_, v_includeDelayed_950_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_980_) == 0)
{
uint8_t v___x_981_; lean_object* v___x_982_; 
lean_dec_ref_known(v___x_980_, 1);
v___x_981_ = 0;
v___x_982_ = l_Lean_LocalDecl_value_x3f(v_val_977_, v___x_981_);
if (lean_obj_tag(v___x_982_) == 1)
{
lean_object* v_val_983_; lean_object* v___x_984_; 
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_983_, v_includeDelayed_950_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec_ref_known(v___x_984_, 1);
v_a_969_ = v___x_978_;
goto v___jp_968_;
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_del_object(v___x_965_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_dec(v___x_982_);
v_a_969_ = v___x_978_;
goto v___jp_968_;
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_del_object(v___x_965_);
v_a_993_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_980_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_980_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
v___jp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v_a_969_);
lean_ctor_set(v___x_965_, 0, v___x_967_);
v___x_971_ = v___x_965_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_a_969_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; 
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_953_, v___x_972_);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_950_, v_as_951_, v_sz_952_, v___x_973_, v___x_971_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(lean_object* v_init_1003_, uint8_t v_includeDelayed_1004_, lean_object* v_n_1005_, lean_object* v_b_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
if (lean_obj_tag(v_n_1005_) == 0)
{
lean_object* v_cs_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; size_t v_sz_1016_; size_t v___x_1017_; lean_object* v___x_1018_; 
v_cs_1013_ = lean_ctor_get(v_n_1005_, 0);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v_b_1006_);
v_sz_1016_ = lean_array_size(v_cs_1013_);
v___x_1017_ = ((size_t)0ULL);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_1003_, v_includeDelayed_1004_, v_cs_1013_, v_sz_1016_, v___x_1017_, v___x_1015_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1033_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1033_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1033_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_fst_1023_; 
v_fst_1023_ = lean_ctor_get(v_a_1019_, 0);
if (lean_obj_tag(v_fst_1023_) == 0)
{
lean_object* v_snd_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v_snd_1024_ = lean_ctor_get(v_a_1019_, 1);
lean_inc(v_snd_1024_);
lean_dec(v_a_1019_);
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_snd_1024_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1025_);
v___x_1027_ = v___x_1021_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1031_; 
lean_inc_ref(v_fst_1023_);
lean_dec(v_a_1019_);
v_val_1029_ = lean_ctor_get(v_fst_1023_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v_fst_1023_, 1);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_val_1029_);
v___x_1031_ = v___x_1021_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_val_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1018_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1018_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_vs_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; size_t v_sz_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v_vs_1042_ = lean_ctor_get(v_n_1005_, 0);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v_b_1006_);
v_sz_1045_ = lean_array_size(v_vs_1042_);
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_1004_, v_vs_1042_, v_sz_1045_, v___x_1046_, v___x_1044_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1062_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1062_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1062_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_fst_1052_; 
v_fst_1052_ = lean_ctor_get(v_a_1048_, 0);
if (lean_obj_tag(v_fst_1052_) == 0)
{
lean_object* v_snd_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v_snd_1053_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_snd_1053_);
lean_dec(v_a_1048_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_snd_1053_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1054_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1060_; 
lean_inc_ref(v_fst_1052_);
lean_dec(v_a_1048_);
v_val_1058_ = lean_ctor_get(v_fst_1052_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v_fst_1052_, 1);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v_val_1058_);
v___x_1060_ = v___x_1050_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_val_1058_);
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
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1047_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1047_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(uint8_t v_includeDelayed_1071_, lean_object* v_as_1072_, size_t v_sz_1073_, size_t v_i_1074_, lean_object* v_b_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_usize_dec_lt(v_i_1074_, v_sz_1073_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_b_1075_);
return v___x_1083_;
}
else
{
lean_object* v_snd_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1122_; 
v_snd_1084_ = lean_ctor_get(v_b_1075_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_b_1075_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_b_1075_, 0);
lean_dec(v_unused_1123_);
v___x_1086_ = v_b_1075_;
v_isShared_1087_ = v_isSharedCheck_1122_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_snd_1084_);
lean_dec(v_b_1075_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1122_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v_a_1090_; lean_object* v_a_1097_; 
v___x_1088_ = lean_box(0);
v_a_1097_ = lean_array_uget_borrowed(v_as_1072_, v_i_1074_);
if (lean_obj_tag(v_a_1097_) == 0)
{
v_a_1090_ = v_snd_1084_;
goto v___jp_1089_;
}
else
{
lean_object* v_val_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_snd_1084_);
v_val_1098_ = lean_ctor_get(v_a_1097_, 0);
v___x_1099_ = lean_box(0);
v___x_1100_ = l_Lean_LocalDecl_type(v_val_1098_);
v___x_1101_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1100_, v_includeDelayed_1071_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1101_) == 0)
{
uint8_t v___x_1102_; lean_object* v___x_1103_; 
lean_dec_ref_known(v___x_1101_, 1);
v___x_1102_ = 0;
v___x_1103_ = l_Lean_LocalDecl_value_x3f(v_val_1098_, v___x_1102_);
if (lean_obj_tag(v___x_1103_) == 1)
{
lean_object* v_val_1104_; lean_object* v___x_1105_; 
v_val_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1104_, v_includeDelayed_1071_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_dec_ref_known(v___x_1105_, 1);
v_a_1090_ = v___x_1099_;
goto v___jp_1089_;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_del_object(v___x_1086_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_dec(v___x_1103_);
v_a_1090_ = v___x_1099_;
goto v___jp_1089_;
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_del_object(v___x_1086_);
v_a_1114_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1101_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1101_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
v___jp_1089_:
{
lean_object* v___x_1092_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v_a_1090_);
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1092_ = v___x_1086_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_a_1090_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
size_t v___x_1093_; size_t v___x_1094_; 
v___x_1093_ = ((size_t)1ULL);
v___x_1094_ = lean_usize_add(v_i_1074_, v___x_1093_);
v_i_1074_ = v___x_1094_;
v_b_1075_ = v___x_1092_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(uint8_t v_includeDelayed_1124_, lean_object* v_as_1125_, size_t v_sz_1126_, size_t v_i_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_usize_dec_lt(v_i_1127_, v_sz_1126_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_b_1128_);
return v___x_1136_;
}
else
{
lean_object* v_snd_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1175_; 
v_snd_1137_ = lean_ctor_get(v_b_1128_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_b_1128_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v_b_1128_, 0);
lean_dec(v_unused_1176_);
v___x_1139_ = v_b_1128_;
v_isShared_1140_ = v_isSharedCheck_1175_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_snd_1137_);
lean_dec(v_b_1128_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1175_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v_a_1143_; lean_object* v_a_1150_; 
v___x_1141_ = lean_box(0);
v_a_1150_ = lean_array_uget_borrowed(v_as_1125_, v_i_1127_);
if (lean_obj_tag(v_a_1150_) == 0)
{
v_a_1143_ = v_snd_1137_;
goto v___jp_1142_;
}
else
{
lean_object* v_val_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec(v_snd_1137_);
v_val_1151_ = lean_ctor_get(v_a_1150_, 0);
v___x_1152_ = lean_box(0);
v___x_1153_ = l_Lean_LocalDecl_type(v_val_1151_);
v___x_1154_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1153_, v_includeDelayed_1124_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1154_) == 0)
{
uint8_t v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref_known(v___x_1154_, 1);
v___x_1155_ = 0;
v___x_1156_ = l_Lean_LocalDecl_value_x3f(v_val_1151_, v___x_1155_);
if (lean_obj_tag(v___x_1156_) == 1)
{
lean_object* v_val_1157_; lean_object* v___x_1158_; 
v_val_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_val_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1157_, v_includeDelayed_1124_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_dec_ref_known(v___x_1158_, 1);
v_a_1143_ = v___x_1152_;
goto v___jp_1142_;
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_del_object(v___x_1139_);
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_dec(v___x_1156_);
v_a_1143_ = v___x_1152_;
goto v___jp_1142_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_del_object(v___x_1139_);
v_a_1167_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1154_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1154_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
v___jp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_a_1143_);
lean_ctor_set(v___x_1139_, 0, v___x_1141_);
v___x_1145_ = v___x_1139_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_a_1143_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = ((size_t)1ULL);
v___x_1147_ = lean_usize_add(v_i_1127_, v___x_1146_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_1124_, v_as_1125_, v_sz_1126_, v___x_1147_, v___x_1145_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(uint8_t v_includeDelayed_1177_, lean_object* v_t_1178_, lean_object* v_init_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_root_1186_; lean_object* v_tail_1187_; lean_object* v___x_1188_; 
v_root_1186_ = lean_ctor_get(v_t_1178_, 0);
v_tail_1187_ = lean_ctor_get(v_t_1178_, 1);
v___x_1188_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1179_, v_includeDelayed_1177_, v_root_1186_, v_init_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1225_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1225_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1225_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
if (lean_obj_tag(v_a_1189_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; 
v_a_1193_ = lean_ctor_get(v_a_1189_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v_a_1189_, 1);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v_a_1193_);
v___x_1195_ = v___x_1191_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; size_t v_sz_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
lean_del_object(v___x_1191_);
v_a_1197_ = lean_ctor_get(v_a_1189_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v_a_1189_, 1);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_a_1197_);
v_sz_1200_ = lean_array_size(v_tail_1187_);
v___x_1201_ = ((size_t)0ULL);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_1177_, v_tail_1187_, v_sz_1200_, v___x_1201_, v___x_1199_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1216_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1216_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1216_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_fst_1207_; 
v_fst_1207_ = lean_ctor_get(v_a_1203_, 0);
if (lean_obj_tag(v_fst_1207_) == 0)
{
lean_object* v_snd_1208_; lean_object* v___x_1210_; 
v_snd_1208_ = lean_ctor_get(v_a_1203_, 1);
lean_inc(v_snd_1208_);
lean_dec(v_a_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v_snd_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_snd_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
lean_object* v_val_1212_; lean_object* v___x_1214_; 
lean_inc_ref(v_fst_1207_);
lean_dec(v_a_1203_);
v_val_1212_ = lean_ctor_get(v_fst_1207_, 0);
lean_inc(v_val_1212_);
lean_dec_ref_known(v_fst_1207_, 1);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v_val_1212_);
v___x_1214_ = v___x_1205_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_val_1212_);
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
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_a_1217_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1202_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1202_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1188_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1188_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object* v_mvarId_1234_, uint8_t v_includeDelayed_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_toCold_1242_; lean_object* v_currRecDepth_1243_; lean_object* v_ref_1244_; uint16_t v_optionFlags_1245_; uint8_t v_suppressElabErrors_1246_; uint8_t v_isRecordingDeps_1247_; lean_object* v_maxRecDepth_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_toCold_1242_ = lean_ctor_get(v_a_1239_, 0);
lean_inc_ref(v_toCold_1242_);
v_currRecDepth_1243_ = lean_ctor_get(v_a_1239_, 1);
lean_inc(v_currRecDepth_1243_);
v_ref_1244_ = lean_ctor_get(v_a_1239_, 2);
lean_inc(v_ref_1244_);
v_optionFlags_1245_ = lean_ctor_get_uint16(v_a_1239_, sizeof(void*)*3);
v_suppressElabErrors_1246_ = lean_ctor_get_uint8(v_a_1239_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1247_ = lean_ctor_get_uint8(v_a_1239_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_1239_);
v_maxRecDepth_1303_ = lean_ctor_get(v_toCold_1242_, 3);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_nat_dec_eq(v_maxRecDepth_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_nat_dec_eq(v_currRecDepth_1243_, v_maxRecDepth_1303_);
if (v___x_1306_ == 0)
{
goto v___jp_1248_;
}
else
{
lean_object* v___x_1307_; 
lean_dec(v_currRecDepth_1243_);
lean_dec_ref(v_toCold_1242_);
lean_dec(v_mvarId_1234_);
v___x_1307_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1244_);
return v___x_1307_;
}
}
else
{
goto v___jp_1248_;
}
v___jp_1248_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_nat_add(v_currRecDepth_1243_, v___x_1249_);
lean_dec(v_currRecDepth_1243_);
v___x_1251_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1251_, 0, v_toCold_1242_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
lean_ctor_set(v___x_1251_, 2, v_ref_1244_);
lean_ctor_set_uint16(v___x_1251_, sizeof(void*)*3, v_optionFlags_1245_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*3 + 2, v_suppressElabErrors_1246_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*3 + 3, v_isRecordingDeps_1247_);
lean_inc(v_mvarId_1234_);
v___x_1252_ = l_Lean_MVarId_getDecl(v_mvarId_1234_, v_a_1237_, v_a_1238_, v___x_1251_, v_a_1240_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_lctx_1254_; lean_object* v_type_1255_; lean_object* v___x_1256_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v_lctx_1254_ = lean_ctor_get(v_a_1253_, 1);
lean_inc_ref(v_lctx_1254_);
v_type_1255_ = lean_ctor_get(v_a_1253_, 2);
lean_inc_ref(v_type_1255_);
lean_dec(v_a_1253_);
v___x_1256_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_type_1255_, v_includeDelayed_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v___x_1251_, v_a_1240_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_decls_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec_ref_known(v___x_1256_, 1);
v_decls_1257_ = lean_ctor_get(v_lctx_1254_, 1);
lean_inc_ref(v_decls_1257_);
lean_dec_ref(v_lctx_1254_);
v___x_1258_ = lean_box(0);
v___x_1259_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_1235_, v_decls_1257_, v___x_1258_, v_a_1236_, v_a_1237_, v_a_1238_, v___x_1251_, v_a_1240_);
lean_dec_ref(v_decls_1257_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1259_, 1);
v___x_1260_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1234_, v_a_1238_);
lean_dec(v_mvarId_1234_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1286_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1286_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1286_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
if (lean_obj_tag(v_a_1261_) == 1)
{
lean_object* v_val_1265_; lean_object* v_mvarIdPending_1266_; lean_object* v___x_1267_; 
lean_del_object(v___x_1263_);
v_val_1265_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v_a_1261_, 1);
v_mvarIdPending_1266_ = lean_ctor_get(v_val_1265_, 1);
lean_inc(v_mvarIdPending_1266_);
lean_dec(v_val_1265_);
v___x_1267_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarIdPending_1266_, v_a_1238_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; uint8_t v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = lean_unbox(v_a_1268_);
lean_dec(v_a_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_st_ref_take(v_a_1236_);
lean_inc(v_mvarIdPending_1266_);
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_1270_, v_mvarIdPending_1266_, v___x_1258_);
v___x_1272_ = lean_st_ref_put(v_a_1236_, v___x_1271_);
v_mvarId_1234_ = v_mvarIdPending_1266_;
v_a_1239_ = v___x_1251_;
goto _start;
}
else
{
v_mvarId_1234_ = v_mvarIdPending_1266_;
v_a_1239_ = v___x_1251_;
goto _start;
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_mvarIdPending_1266_);
lean_dec_ref_known(v___x_1251_, 3);
v_a_1275_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1267_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1267_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v___x_1284_; 
lean_dec(v_a_1261_);
lean_dec_ref_known(v___x_1251_, 3);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1258_);
v___x_1284_ = v___x_1263_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1258_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref_known(v___x_1251_, 3);
v_a_1287_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1260_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1260_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1251_, 3);
lean_dec(v_mvarId_1234_);
return v___x_1259_;
}
}
else
{
lean_dec_ref(v_lctx_1254_);
lean_dec_ref_known(v___x_1251_, 3);
lean_dec(v_mvarId_1234_);
return v___x_1256_;
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref_known(v___x_1251_, 3);
lean_dec(v_mvarId_1234_);
v_a_1295_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1252_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1252_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(lean_object* v_as_1308_, size_t v_i_1309_, size_t v_stop_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_eq(v_i_1309_, v_stop_1310_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_array_uget_borrowed(v_as_1308_, v_i_1309_);
lean_inc_ref(v___y_1315_);
lean_inc(v___x_1319_);
v___x_1320_ = l___private_Lean_Meta_CollectMVars_0__go(v___x_1319_, v___x_1318_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; size_t v___x_1322_; size_t v___x_1323_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = lean_usize_add(v_i_1309_, v___x_1322_);
v_i_1309_ = v___x_1323_;
v_b_1311_ = v_a_1321_;
goto _start;
}
else
{
return v___x_1320_;
}
}
else
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_b_1311_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object* v_as_1326_, lean_object* v_i_1327_, lean_object* v_stop_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
size_t v_i_boxed_1336_; size_t v_stop_boxed_1337_; lean_object* v_res_1338_; 
v_i_boxed_1336_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_stop_boxed_1337_ = lean_unbox_usize(v_stop_1328_);
lean_dec(v_stop_1328_);
v_res_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_as_1326_, v_i_boxed_1336_, v_stop_boxed_1337_, v_b_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v_as_1326_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(lean_object* v_init_1339_, lean_object* v_includeDelayed_1340_, lean_object* v_as_1341_, lean_object* v_sz_1342_, lean_object* v_i_1343_, lean_object* v_b_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_includeDelayed_boxed_1351_; size_t v_sz_boxed_1352_; size_t v_i_boxed_1353_; lean_object* v_res_1354_; 
v_includeDelayed_boxed_1351_ = lean_unbox(v_includeDelayed_1340_);
v_sz_boxed_1352_ = lean_unbox_usize(v_sz_1342_);
lean_dec(v_sz_1342_);
v_i_boxed_1353_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_1339_, v_includeDelayed_boxed_1351_, v_as_1341_, v_sz_boxed_1352_, v_i_boxed_1353_, v_b_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v_as_1341_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(lean_object* v_includeDelayed_1355_, lean_object* v_t_1356_, lean_object* v_init_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v_includeDelayed_boxed_1364_; lean_object* v_res_1365_; 
v_includeDelayed_boxed_1364_ = lean_unbox(v_includeDelayed_1355_);
v_res_1365_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_boxed_1364_, v_t_1356_, v_init_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v_t_1356_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object* v_e_1366_, lean_object* v_includeDelayed_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
uint8_t v_includeDelayed_boxed_1374_; lean_object* v_res_1375_; 
v_includeDelayed_boxed_1374_ = lean_unbox(v_includeDelayed_1367_);
v_res_1375_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1366_, v_includeDelayed_boxed_1374_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object* v_includeDelayed_1376_, lean_object* v_as_1377_, lean_object* v_sz_1378_, lean_object* v_i_1379_, lean_object* v_b_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v_includeDelayed_boxed_1387_; size_t v_sz_boxed_1388_; size_t v_i_boxed_1389_; lean_object* v_res_1390_; 
v_includeDelayed_boxed_1387_ = lean_unbox(v_includeDelayed_1376_);
v_sz_boxed_1388_ = lean_unbox_usize(v_sz_1378_);
lean_dec(v_sz_1378_);
v_i_boxed_1389_ = lean_unbox_usize(v_i_1379_);
lean_dec(v_i_1379_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_boxed_1387_, v_as_1377_, v_sz_boxed_1388_, v_i_boxed_1389_, v_b_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v_as_1377_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object* v_includeDelayed_1391_, lean_object* v_as_1392_, lean_object* v_sz_1393_, lean_object* v_i_1394_, lean_object* v_b_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v_includeDelayed_boxed_1402_; size_t v_sz_boxed_1403_; size_t v_i_boxed_1404_; lean_object* v_res_1405_; 
v_includeDelayed_boxed_1402_ = lean_unbox(v_includeDelayed_1391_);
v_sz_boxed_1403_ = lean_unbox_usize(v_sz_1393_);
lean_dec(v_sz_1393_);
v_i_boxed_1404_ = lean_unbox_usize(v_i_1394_);
lean_dec(v_i_1394_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_boxed_1402_, v_as_1392_, v_sz_boxed_1403_, v_i_boxed_1404_, v_b_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v_as_1392_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object* v_includeDelayed_1406_, lean_object* v_as_1407_, lean_object* v_sz_1408_, lean_object* v_i_1409_, lean_object* v_b_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v_includeDelayed_boxed_1417_; size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v_includeDelayed_boxed_1417_ = lean_unbox(v_includeDelayed_1406_);
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1408_);
lean_dec(v_sz_1408_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1409_);
lean_dec(v_i_1409_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_boxed_1417_, v_as_1407_, v_sz_boxed_1418_, v_i_boxed_1419_, v_b_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v_as_1407_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object* v_includeDelayed_1421_, lean_object* v_as_1422_, lean_object* v_sz_1423_, lean_object* v_i_1424_, lean_object* v_b_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_includeDelayed_boxed_1432_; size_t v_sz_boxed_1433_; size_t v_i_boxed_1434_; lean_object* v_res_1435_; 
v_includeDelayed_boxed_1432_ = lean_unbox(v_includeDelayed_1421_);
v_sz_boxed_1433_ = lean_unbox_usize(v_sz_1423_);
lean_dec(v_sz_1423_);
v_i_boxed_1434_ = lean_unbox_usize(v_i_1424_);
lean_dec(v_i_1424_);
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_boxed_1432_, v_as_1422_, v_sz_boxed_1433_, v_i_boxed_1434_, v_b_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v_as_1422_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object* v_init_1436_, lean_object* v_includeDelayed_1437_, lean_object* v_n_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v_includeDelayed_boxed_1446_; lean_object* v_res_1447_; 
v_includeDelayed_boxed_1446_ = lean_unbox(v_includeDelayed_1437_);
v_res_1447_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1436_, v_includeDelayed_boxed_1446_, v_n_1438_, v_b_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v_n_1438_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go___boxed(lean_object* v_mvarId_1448_, lean_object* v_includeDelayed_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
uint8_t v_includeDelayed_boxed_1456_; lean_object* v_res_1457_; 
v_includeDelayed_boxed_1456_ = lean_unbox(v_includeDelayed_1449_);
v_res_1457_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1448_, v_includeDelayed_boxed_1456_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
lean_dec(v_a_1454_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(lean_object* v_mvarId_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1458_, v___y_1461_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(lean_object* v_mvarId_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(v_mvarId_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec(v_mvarId_1466_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_object* v_00_u03b1_1474_, lean_object* v_ref_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1475_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_ref_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(v_00_u03b1_1483_, v_ref_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(lean_object* v_00_u03b2_1492_, lean_object* v_m_1493_, lean_object* v_a_1494_, lean_object* v_b_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_1493_, v_a_1494_, v_b_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(lean_object* v_mvarId_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_1497_, v___y_1500_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(lean_object* v_mvarId_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_mvarId_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec(v_mvarId_1505_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(lean_object* v_mvarId_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_1513_, v___y_1516_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(lean_object* v_mvarId_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec(v_mvarId_1521_);
return v_res_1528_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_object* v_00_u03b2_1529_, lean_object* v_a_1530_, lean_object* v_x_1531_){
_start:
{
uint8_t v___x_1532_; 
v___x_1532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_1530_, v_x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1533_, lean_object* v_a_1534_, lean_object* v_x_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(v_00_u03b2_1533_, v_a_1534_, v_x_1535_);
lean_dec(v_x_1535_);
lean_dec(v_a_1534_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1(lean_object* v_00_u03b2_1538_, lean_object* v_data_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_data_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1541_, lean_object* v_i_1542_, lean_object* v_source_1543_, lean_object* v_target_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v_i_1542_, v_source_1543_, v_target_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_x_1547_, v_x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies(lean_object* v_mvarId_1550_, uint8_t v_includeDelayed_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1558_ = lean_st_mk_ref(v___x_1557_);
lean_inc_ref(v_a_1554_);
v___x_1559_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1550_, v_includeDelayed_1551_, v___x_1558_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v___x_1559_, 0);
lean_dec(v_unused_1568_);
v___x_1561_ = v___x_1559_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v___x_1559_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_st_ref_get(v___x_1558_);
lean_dec(v___x_1558_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v___x_1558_);
v_a_1569_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1559_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1559_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object* v_mvarId_1577_, lean_object* v_includeDelayed_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
uint8_t v_includeDelayed_boxed_1584_; lean_object* v_res_1585_; 
v_includeDelayed_boxed_1584_ = lean_unbox(v_includeDelayed_1578_);
v_res_1585_ = l_Lean_MVarId_getMVarDependencies(v_mvarId_1577_, v_includeDelayed_boxed_1584_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies(lean_object* v_e_1586_, uint8_t v_includeDelayed_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1594_ = lean_st_mk_ref(v___x_1593_);
v___x_1595_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1586_, v_includeDelayed_1587_, v___x_1594_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1603_; 
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; 
v_unused_1604_ = lean_ctor_get(v___x_1595_, 0);
lean_dec(v_unused_1604_);
v___x_1597_ = v___x_1595_;
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v___x_1595_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = lean_st_ref_get(v___x_1594_);
lean_dec(v___x_1594_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1599_);
v___x_1601_ = v___x_1597_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v___x_1594_);
v_a_1605_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1595_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1595_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies___boxed(lean_object* v_e_1613_, lean_object* v_includeDelayed_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
uint8_t v_includeDelayed_boxed_1620_; lean_object* v_res_1621_; 
v_includeDelayed_boxed_1620_ = lean_unbox(v_includeDelayed_1614_);
v_res_1621_ = l_Lean_Expr_getMVarDependencies(v_e_1613_, v_includeDelayed_boxed_1620_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
return v_res_1621_;
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
