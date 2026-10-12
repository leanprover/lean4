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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_31_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___boxed(lean_object* v_e_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(v_e_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
return v_res_47_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(lean_object* v_mvarId_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; lean_object* v_mctx_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = lean_st_ref_get(v___y_49_);
v_mctx_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc_ref(v_mctx_52_);
lean_dec(v___x_51_);
v___x_53_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_52_, v_mvarId_48_);
lean_dec_ref(v_mctx_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_48_ = stack[0].m_obj;
lean_object* v___y_49_ = stack[1].m_obj;
lean_object* v_res_55_;
v_res_55_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v_mvarId_48_, v___y_49_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg___boxed(lean_object* v_mvarId_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v_mvarId_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec(v_mvarId_56_);
return v_res_59_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(lean_object* v_mvarId_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v_mvarId_60_, v___y_63_);
return v___x_67_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_60_ = stack[0].m_obj;
lean_object* v___y_61_ = stack[1].m_obj;
lean_object* v___y_62_ = stack[2].m_obj;
lean_object* v___y_63_ = stack[3].m_obj;
lean_object* v___y_64_ = stack[4].m_obj;
lean_object* v___y_65_ = stack[5].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(v_mvarId_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___boxed(lean_object* v_mvarId_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(v_mvarId_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec(v_mvarId_69_);
return v_res_76_;
}
}
lean_object* l_Lean_Meta_collectMVars(lean_object* v_e_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_77_, v_a_80_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v_result_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_result_91_; lean_object* v_lower_93_; lean_object* v_upper_94_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v___x_84_, 1);
v___x_86_ = lean_st_ref_get(v_a_78_);
v_result_87_ = lean_ctor_get(v___x_86_, 1);
v___x_88_ = lean_array_get_size(v_result_87_);
v___x_89_ = l_Lean_Expr_collectMVars(v___x_86_, v_a_85_);
lean_inc_ref(v___x_89_);
v___x_90_ = lean_st_ref_swap(v_a_78_, v___x_89_);
lean_dec(v___x_90_);
v_result_91_ = lean_ctor_get(v___x_89_, 1);
lean_inc_ref(v_result_91_);
lean_dec_ref(v___x_89_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_array_get_size(v_result_91_);
v___x_108_ = lean_nat_dec_le(v___x_88_, v___x_106_);
if (v___x_108_ == 0)
{
v_lower_93_ = v___x_88_;
v_upper_94_ = v___x_107_;
goto v___jp_92_;
}
else
{
v_lower_93_ = v___x_106_;
v_upper_94_ = v___x_107_;
goto v___jp_92_;
}
v___jp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = l_Array_toSubarray___redArg(v_result_91_, v_lower_93_, v_upper_94_);
v___x_96_ = lean_box(0);
v___x_97_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v___x_95_, v___x_96_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_97_, 0);
lean_dec(v_unused_105_);
v___x_99_ = v___x_97_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_dec(v___x_97_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_96_);
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_96_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
return v___x_97_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_109_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_84_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_84_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_collectMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_77_ = stack[0].m_obj;
lean_object* v_a_78_ = stack[1].m_obj;
lean_object* v_a_79_ = stack[2].m_obj;
lean_object* v_a_80_ = stack[3].m_obj;
lean_object* v_a_81_ = stack[4].m_obj;
lean_object* v_a_82_ = stack[5].m_obj;
lean_object* v_res_117_;
v_res_117_ = l_Lean_Meta_collectMVars(v_e_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
stack->m_obj
 = v_res_117_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(lean_object* v_a_118_, lean_object* v_b_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_array_126_; lean_object* v_start_127_; lean_object* v_stop_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_157_; 
v_array_126_ = lean_ctor_get(v_a_118_, 0);
v_start_127_ = lean_ctor_get(v_a_118_, 1);
v_stop_128_ = lean_ctor_get(v_a_118_, 2);
v_isSharedCheck_157_ = !lean_is_exclusive(v_a_118_);
if (v_isSharedCheck_157_ == 0)
{
v___x_130_ = v_a_118_;
v_isShared_131_ = v_isSharedCheck_157_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_stop_128_);
lean_inc(v_start_127_);
lean_inc(v_array_126_);
lean_dec(v_a_118_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_157_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_lt(v_start_127_, v_stop_128_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_del_object(v___x_130_);
lean_dec(v_stop_128_);
lean_dec(v_start_127_);
lean_dec_ref(v_array_126_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_b_119_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_134_ = lean_box(0);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_add(v_start_127_, v___x_135_);
lean_inc_ref(v_array_126_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_136_);
v___x_138_ = v___x_130_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_array_126_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_stop_128_);
v___x_138_ = v_reuseFailAlloc_156_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_array_fget(v_array_126_, v_start_127_);
lean_dec(v_start_127_);
lean_dec_ref(v_array_126_);
v___x_140_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v___x_139_, v___y_122_);
lean_dec(v___x_139_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
if (lean_obj_tag(v_a_141_) == 0)
{
v_a_118_ = v___x_138_;
v_b_119_ = v___x_134_;
goto _start;
}
else
{
lean_object* v_val_143_; lean_object* v_mvarIdPending_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_val_143_ = lean_ctor_get(v_a_141_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v_a_141_, 1);
v_mvarIdPending_144_ = lean_ctor_get(v_val_143_, 1);
lean_inc(v_mvarIdPending_144_);
lean_dec(v_val_143_);
v___x_145_ = l_Lean_mkMVar(v_mvarIdPending_144_);
v___x_146_ = l_Lean_Meta_collectMVars(v___x_145_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_dec_ref_known(v___x_146_, 1);
v_a_118_ = v___x_138_;
v_b_119_ = v___x_134_;
goto _start;
}
else
{
lean_dec_ref(v___x_138_);
return v___x_146_;
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec_ref(v___x_138_);
v_a_148_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_140_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_140_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_118_ = stack[0].m_obj;
lean_object* v_b_119_ = stack[1].m_obj;
lean_object* v___y_120_ = stack[2].m_obj;
lean_object* v___y_121_ = stack[3].m_obj;
lean_object* v___y_122_ = stack[4].m_obj;
lean_object* v___y_123_ = stack[5].m_obj;
lean_object* v___y_124_ = stack[6].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_118_, v_b_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___boxed(lean_object* v_a_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_159_, v_b_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars___boxed(lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Meta_collectMVars(v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
return v_res_175_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(lean_object* v_inst_176_, lean_object* v_R_177_, lean_object* v_a_178_, lean_object* v_b_179_, lean_object* v_c_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_178_, v_b_179_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_178_ = stack[2].m_obj;
lean_object* v_b_179_ = stack[3].m_obj;
lean_object* v___y_181_ = stack[5].m_obj;
lean_object* v___y_182_ = stack[6].m_obj;
lean_object* v___y_183_ = stack[7].m_obj;
lean_object* v___y_184_ = stack[8].m_obj;
lean_object* v___y_185_ = stack[9].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(lean_box(0), lean_box(0), v_a_178_, v_b_179_, lean_box(0), v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___boxed(lean_object* v_inst_189_, lean_object* v_R_190_, lean_object* v_a_191_, lean_object* v_b_192_, lean_object* v_c_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(v_inst_189_, v_R_190_, v_a_191_, v_b_192_, v_c_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
return v_res_200_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__0(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_box(0);
v___x_202_ = lean_unsigned_to_nat(16u);
v___x_203_ = lean_mk_array(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__0, &l_Lean_Meta_getMVars___closed__0_once, _init_l_Lean_Meta_getMVars___closed__0);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_210_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__1, &l_Lean_Meta_getMVars___closed__1_once, _init_l_Lean_Meta_getMVars___closed__1);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
return v___x_211_;
}
}
lean_object* l_Lean_Meta_getMVars(lean_object* v_e_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_219_ = lean_st_mk_ref(v___x_218_);
v___x_220_ = l_Lean_Meta_collectMVars(v_e_212_, v___x_219_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_229_; 
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___x_220_, 0);
lean_dec(v_unused_230_);
v___x_222_ = v___x_220_;
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
else
{
lean_dec(v___x_220_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v_result_225_; lean_object* v___x_227_; 
v___x_224_ = lean_st_ref_get(v___x_219_);
lean_dec(v___x_219_);
v_result_225_ = lean_ctor_get(v___x_224_, 1);
lean_inc_ref(v_result_225_);
lean_dec(v___x_224_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v_result_225_);
v___x_227_ = v___x_222_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_result_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec(v___x_219_);
v_a_231_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_220_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_220_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_212_ = stack[0].m_obj;
lean_object* v_a_213_ = stack[1].m_obj;
lean_object* v_a_214_ = stack[2].m_obj;
lean_object* v_a_215_ = stack[3].m_obj;
lean_object* v_a_216_ = stack[4].m_obj;
lean_object* v_res_239_;
v_res_239_ = l_Lean_Meta_getMVars(v_e_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars___boxed(lean_object* v_e_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_getMVars(v_e_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_246_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_247_, lean_object* v_i_248_, lean_object* v_k_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_array_get_size(v_keys_247_);
v___x_251_ = lean_nat_dec_lt(v_i_248_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v_i_248_);
return v___x_251_;
}
else
{
lean_object* v_k_x27_252_; uint8_t v___x_253_; 
v_k_x27_252_ = lean_array_fget_borrowed(v_keys_247_, v_i_248_);
v___x_253_ = l_Lean_instBEqMVarId_beq(v_k_249_, v_k_x27_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_nat_add(v_i_248_, v___x_254_);
lean_dec(v_i_248_);
v_i_248_ = v___x_255_;
goto _start;
}
else
{
lean_dec(v_i_248_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_247_ = stack[0].m_obj;
lean_object* v_i_248_ = stack[1].m_obj;
lean_object* v_k_249_ = stack[2].m_obj;
uint8_t v_res_257_;
v_res_257_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_247_, v_i_248_, v_k_249_);
stack->m_num = v_res_257_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_258_, lean_object* v_i_259_, lean_object* v_k_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_258_, v_i_259_, v_k_260_);
lean_dec(v_k_260_);
lean_dec_ref(v_keys_258_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_263_, size_t v_x_264_, lean_object* v_x_265_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_es_266_; lean_object* v___x_267_; size_t v___x_268_; size_t v___x_269_; lean_object* v_j_270_; lean_object* v___x_271_; 
v_es_266_ = lean_ctor_get(v_x_263_, 0);
v___x_267_ = lean_box(2);
v___x_268_ = ((size_t)31ULL);
v___x_269_ = lean_usize_land(v_x_264_, v___x_268_);
v_j_270_ = lean_usize_to_nat(v___x_269_);
v___x_271_ = lean_array_get_borrowed(v___x_267_, v_es_266_, v_j_270_);
lean_dec(v_j_270_);
switch(lean_obj_tag(v___x_271_))
{
case 0:
{
lean_object* v_key_272_; uint8_t v___x_273_; 
v_key_272_ = lean_ctor_get(v___x_271_, 0);
v___x_273_ = l_Lean_instBEqMVarId_beq(v_x_265_, v_key_272_);
return v___x_273_;
}
case 1:
{
lean_object* v_node_274_; size_t v___x_275_; size_t v___x_276_; 
v_node_274_ = lean_ctor_get(v___x_271_, 0);
v___x_275_ = ((size_t)5ULL);
v___x_276_ = lean_usize_shift_right(v_x_264_, v___x_275_);
v_x_263_ = v_node_274_;
v_x_264_ = v___x_276_;
goto _start;
}
default: 
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
}
}
else
{
lean_object* v_ks_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_ks_279_ = lean_ctor_get(v_x_263_, 0);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_279_, v___x_280_, v_x_265_);
return v___x_281_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_263_ = stack[0].m_obj;
size_t v_x_264_ = stack[1].m_num;
lean_object* v_x_265_ = stack[2].m_obj;
uint8_t v_res_282_;
v_res_282_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_263_, v_x_264_, v_x_265_);
stack->m_num = v_res_282_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
size_t v_x_1292__boxed_286_; uint8_t v_res_287_; lean_object* v_r_288_; 
v_x_1292__boxed_286_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_res_287_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_283_, v_x_1292__boxed_286_, v_x_285_);
lean_dec(v_x_285_);
lean_dec_ref(v_x_283_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
uint64_t v___x_291_; size_t v___x_292_; uint8_t v___x_293_; 
v___x_291_ = l_Lean_instHashableMVarId_hash(v_x_290_);
v___x_292_ = lean_uint64_to_usize(v___x_291_);
v___x_293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_289_, v___x_292_, v_x_290_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_289_ = stack[0].m_obj;
lean_object* v_x_290_ = stack[1].m_obj;
uint8_t v_res_294_;
v_res_294_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_289_, v_x_290_);
stack->m_num = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg___boxed(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_295_, v_x_296_);
lean_dec(v_x_296_);
lean_dec_ref(v_x_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(lean_object* v_mvarId_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_mctx_303_; lean_object* v_dAssignment_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_302_ = lean_st_ref_get(v___y_300_);
v_mctx_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc_ref(v_mctx_303_);
lean_dec(v___x_302_);
v_dAssignment_304_ = lean_ctor_get(v_mctx_303_, 9);
lean_inc_ref(v_dAssignment_304_);
lean_dec_ref(v_mctx_303_);
v___x_305_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_304_, v_mvarId_299_);
lean_dec_ref(v_dAssignment_304_);
v___x_306_ = lean_box(v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_299_ = stack[0].m_obj;
lean_object* v___y_300_ = stack[1].m_obj;
lean_object* v_res_308_;
v_res_308_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_299_, v___y_300_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(lean_object* v_mvarId_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec(v_mvarId_309_);
return v_res_312_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(lean_object* v_as_313_, size_t v_i_314_, size_t v_stop_315_, lean_object* v_b_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_a_323_; uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_eq(v_i_314_, v_stop_315_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_331_; 
v___x_328_ = lean_array_uget_borrowed(v_as_313_, v_i_314_);
v___x_331_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v___x_328_, v___y_318_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; uint8_t v___x_333_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = lean_unbox(v_a_332_);
lean_dec(v_a_332_);
if (v___x_333_ == 0)
{
goto v___jp_329_;
}
else
{
v_a_323_ = v_b_316_;
goto v___jp_322_;
}
}
else
{
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_334_; uint8_t v___x_335_; 
v_a_334_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_331_, 1);
v___x_335_ = lean_unbox(v_a_334_);
lean_dec(v_a_334_);
if (v___x_335_ == 0)
{
v_a_323_ = v_b_316_;
goto v___jp_322_;
}
else
{
goto v___jp_329_;
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v_b_316_);
v_a_336_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_331_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_331_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
v___jp_329_:
{
lean_object* v___x_330_; 
lean_inc(v___x_328_);
v___x_330_ = lean_array_push(v_b_316_, v___x_328_);
v_a_323_ = v___x_330_;
goto v___jp_322_;
}
}
else
{
lean_object* v___x_344_; 
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_b_316_);
return v___x_344_;
}
v___jp_322_:
{
size_t v___x_324_; size_t v___x_325_; 
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_314_, v___x_324_);
v_i_314_ = v___x_325_;
v_b_316_ = v_a_323_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_313_ = stack[0].m_obj;
size_t v_i_314_ = stack[1].m_num;
size_t v_stop_315_ = stack[2].m_num;
lean_object* v_b_316_ = stack[3].m_obj;
lean_object* v___y_317_ = stack[4].m_obj;
lean_object* v___y_318_ = stack[5].m_obj;
lean_object* v___y_319_ = stack[6].m_obj;
lean_object* v___y_320_ = stack[7].m_obj;
lean_object* v_res_345_;
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_313_, v_i_314_, v_stop_315_, v_b_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1___boxed(lean_object* v_as_346_, lean_object* v_i_347_, lean_object* v_stop_348_, lean_object* v_b_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
size_t v_i_boxed_355_; size_t v_stop_boxed_356_; lean_object* v_res_357_; 
v_i_boxed_355_ = lean_unbox_usize(v_i_347_);
lean_dec(v_i_347_);
v_stop_boxed_356_ = lean_unbox_usize(v_stop_348_);
lean_dec(v_stop_348_);
v_res_357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_346_, v_i_boxed_355_, v_stop_boxed_356_, v_b_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec_ref(v_as_346_);
return v_res_357_;
}
}
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object* v_e_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_getMVars(v_e_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_386_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_386_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_386_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_386_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_array_get_size(v_a_365_);
v___x_371_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_372_ = lean_nat_dec_lt(v___x_369_, v___x_370_);
if (v___x_372_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v_a_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_371_);
v___x_374_ = v___x_367_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_371_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_le(v___x_370_, v___x_370_);
if (v___x_376_ == 0)
{
if (v___x_372_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_a_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_371_);
v___x_378_ = v___x_367_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_371_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
else
{
size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
lean_del_object(v___x_367_);
v___x_380_ = ((size_t)0ULL);
v___x_381_ = lean_usize_of_nat(v___x_370_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_365_, v___x_380_, v___x_381_, v___x_371_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_365_);
return v___x_382_;
}
}
else
{
size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
lean_del_object(v___x_367_);
v___x_383_ = ((size_t)0ULL);
v___x_384_ = lean_usize_of_nat(v___x_370_);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_365_, v___x_383_, v___x_384_, v___x_371_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_365_);
return v___x_385_;
}
}
}
}
else
{
return v___x_364_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getMVarsNoDelayed_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_358_ = stack[0].m_obj;
lean_object* v_a_359_ = stack[1].m_obj;
lean_object* v_a_360_ = stack[2].m_obj;
lean_object* v_a_361_ = stack[3].m_obj;
lean_object* v_a_362_ = stack[4].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Meta_getMVarsNoDelayed(v_e_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Meta_getMVarsNoDelayed(v_e_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
return v_res_394_;
}
}
lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(lean_object* v_mvarId_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_395_, v___y_397_);
return v___x_401_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_395_ = stack[0].m_obj;
lean_object* v___y_396_ = stack[1].m_obj;
lean_object* v___y_397_ = stack[2].m_obj;
lean_object* v___y_398_ = stack[3].m_obj;
lean_object* v___y_399_ = stack[4].m_obj;
lean_object* v_res_402_;
v_res_402_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(v_mvarId_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(lean_object* v_mvarId_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(v_mvarId_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v_mvarId_403_);
return v_res_409_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(lean_object* v_00_u03b2_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint8_t v___x_413_; 
v___x_413_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_411_, v_x_412_);
return v___x_413_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_411_ = stack[1].m_obj;
lean_object* v_x_412_ = stack[2].m_obj;
uint8_t v_res_414_;
v_res_414_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(lean_box(0), v_x_411_, v_x_412_);
stack->m_num = v_res_414_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_415_, lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(v_00_u03b2_415_, v_x_416_, v_x_417_);
lean_dec(v_x_417_);
lean_dec_ref(v_x_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_420_, lean_object* v_x_421_, size_t v_x_422_, lean_object* v_x_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_421_, v_x_422_, v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_421_ = stack[1].m_obj;
size_t v_x_422_ = stack[2].m_num;
lean_object* v_x_423_ = stack[3].m_obj;
uint8_t v_res_425_;
v_res_425_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(lean_box(0), v_x_421_, v_x_422_, v_x_423_);
stack->m_num = v_res_425_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
size_t v_x_1607__boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_x_1607__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(v_00_u03b2_426_, v_x_427_, v_x_1607__boxed_430_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_427_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_heq_436_, lean_object* v_i_437_, lean_object* v_k_438_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_434_, v_i_437_, v_k_438_);
return v___x_439_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_434_ = stack[1].m_obj;
lean_object* v_vals_435_ = stack[2].m_obj;
lean_object* v_i_437_ = stack[4].m_obj;
lean_object* v_k_438_ = stack[5].m_obj;
uint8_t v_res_440_;
v_res_440_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_keys_434_, v_vals_435_, lean_box(0), v_i_437_, v_k_438_);
stack->m_num = v_res_440_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_441_, lean_object* v_keys_442_, lean_object* v_vals_443_, lean_object* v_heq_444_, lean_object* v_i_445_, lean_object* v_k_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_441_, v_keys_442_, v_vals_443_, v_heq_444_, v_i_445_, v_k_446_);
lean_dec(v_k_446_);
lean_dec_ref(v_vals_443_);
lean_dec_ref(v_keys_442_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_x_449_);
return v___x_457_;
}
else
{
lean_object* v_head_458_; lean_object* v_tail_459_; lean_object* v_type_460_; lean_object* v___x_461_; 
v_head_458_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_head_458_);
v_tail_459_ = lean_ctor_get(v_x_450_, 1);
lean_inc(v_tail_459_);
lean_dec_ref_known(v_x_450_, 2);
v_type_460_ = lean_ctor_get(v_head_458_, 1);
lean_inc_ref(v_type_460_);
lean_dec(v_head_458_);
v___x_461_ = l_Lean_Meta_collectMVars(v_type_460_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v_x_449_ = v_a_462_;
v_x_450_ = v_tail_459_;
goto _start;
}
else
{
lean_dec(v_tail_459_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_449_ = stack[0].m_obj;
lean_object* v_x_450_ = stack[1].m_obj;
lean_object* v___y_451_ = stack[2].m_obj;
lean_object* v___y_452_ = stack[3].m_obj;
lean_object* v___y_453_ = stack[4].m_obj;
lean_object* v___y_454_ = stack[5].m_obj;
lean_object* v___y_455_ = stack[6].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_449_, v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_465_, v_x_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
return v_res_473_;
}
}
lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
if (lean_obj_tag(v_x_475_) == 0)
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_x_474_);
return v___x_482_;
}
else
{
lean_object* v_head_483_; lean_object* v_tail_484_; lean_object* v___y_486_; lean_object* v_type_489_; lean_object* v_ctors_490_; lean_object* v___x_491_; 
v_head_483_ = lean_ctor_get(v_x_475_, 0);
lean_inc(v_head_483_);
v_tail_484_ = lean_ctor_get(v_x_475_, 1);
lean_inc(v_tail_484_);
lean_dec_ref_known(v_x_475_, 2);
v_type_489_ = lean_ctor_get(v_head_483_, 1);
lean_inc_ref(v_type_489_);
v_ctors_490_ = lean_ctor_get(v_head_483_, 2);
lean_inc(v_ctors_490_);
lean_dec(v_head_483_);
v___x_491_ = l_Lean_Meta_collectMVars(v_type_489_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_a_492_, v_ctors_490_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
v___y_486_ = v___x_493_;
goto v___jp_485_;
}
else
{
lean_dec(v_ctors_490_);
v___y_486_ = v___x_491_;
goto v___jp_485_;
}
v___jp_485_:
{
if (lean_obj_tag(v___y_486_) == 0)
{
lean_object* v_a_487_; 
v_a_487_ = lean_ctor_get(v___y_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___y_486_, 1);
v_x_474_ = v_a_487_;
v_x_475_ = v_tail_484_;
goto _start;
}
else
{
lean_dec(v_tail_484_);
return v___y_486_;
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_474_ = stack[0].m_obj;
lean_object* v_x_475_ = stack[1].m_obj;
lean_object* v___y_476_ = stack[2].m_obj;
lean_object* v___y_477_ = stack[3].m_obj;
lean_object* v___y_478_ = stack[4].m_obj;
lean_object* v___y_479_ = stack[5].m_obj;
lean_object* v___y_480_ = stack[6].m_obj;
lean_object* v_res_494_;
v_res_494_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_474_, v_x_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
stack->m_obj
 = v_res_494_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_495_, v_x_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
return v_res_503_;
}
}
lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v_x_504_);
return v___x_512_;
}
else
{
lean_object* v_head_513_; lean_object* v_tail_514_; lean_object* v___y_516_; lean_object* v_toConstantVal_519_; lean_object* v_value_520_; lean_object* v_type_521_; lean_object* v___x_522_; 
v_head_513_ = lean_ctor_get(v_x_505_, 0);
lean_inc(v_head_513_);
v_tail_514_ = lean_ctor_get(v_x_505_, 1);
lean_inc(v_tail_514_);
lean_dec_ref_known(v_x_505_, 2);
v_toConstantVal_519_ = lean_ctor_get(v_head_513_, 0);
lean_inc_ref(v_toConstantVal_519_);
v_value_520_ = lean_ctor_get(v_head_513_, 1);
lean_inc_ref(v_value_520_);
lean_dec(v_head_513_);
v_type_521_ = lean_ctor_get(v_toConstantVal_519_, 2);
lean_inc_ref(v_type_521_);
lean_dec_ref(v_toConstantVal_519_);
v___x_522_ = l_Lean_Meta_collectMVars(v_type_521_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; 
lean_dec_ref_known(v___x_522_, 1);
v___x_523_ = l_Lean_Meta_collectMVars(v_value_520_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
v___y_516_ = v___x_523_;
goto v___jp_515_;
}
else
{
lean_dec_ref(v_value_520_);
v___y_516_ = v___x_522_;
goto v___jp_515_;
}
v___jp_515_:
{
if (lean_obj_tag(v___y_516_) == 0)
{
lean_object* v_a_517_; 
v_a_517_ = lean_ctor_get(v___y_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___y_516_, 1);
v_x_504_ = v_a_517_;
v_x_505_ = v_tail_514_;
goto _start;
}
else
{
lean_dec(v_tail_514_);
return v___y_516_;
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_504_ = stack[0].m_obj;
lean_object* v_x_505_ = stack[1].m_obj;
lean_object* v___y_506_ = stack[2].m_obj;
lean_object* v___y_507_ = stack[3].m_obj;
lean_object* v___y_508_ = stack[4].m_obj;
lean_object* v___y_509_ = stack[5].m_obj;
lean_object* v___y_510_ = stack[6].m_obj;
lean_object* v_res_524_;
v_res_524_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_504_, v_x_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_525_, v_x_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
return v_res_533_;
}
}
lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(lean_object* v_d_534_, lean_object* v_a_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
switch(lean_obj_tag(v_d_534_))
{
case 0:
{
lean_object* v_val_542_; lean_object* v_toConstantVal_543_; lean_object* v_type_544_; lean_object* v___x_545_; 
v_val_542_ = lean_ctor_get(v_d_534_, 0);
lean_inc_ref(v_val_542_);
lean_dec_ref_known(v_d_534_, 1);
v_toConstantVal_543_ = lean_ctor_get(v_val_542_, 0);
lean_inc_ref(v_toConstantVal_543_);
lean_dec_ref(v_val_542_);
v_type_544_ = lean_ctor_get(v_toConstantVal_543_, 2);
lean_inc_ref(v_type_544_);
lean_dec_ref(v_toConstantVal_543_);
v___x_545_ = l_Lean_Meta_collectMVars(v_type_544_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_545_;
}
case 4:
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v_a_535_);
return v___x_546_;
}
case 5:
{
lean_object* v_defns_547_; lean_object* v___x_548_; 
v_defns_547_ = lean_ctor_get(v_d_534_, 0);
lean_inc(v_defns_547_);
lean_dec_ref_known(v_d_534_, 1);
v___x_548_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_a_535_, v_defns_547_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_548_;
}
case 6:
{
lean_object* v_types_549_; lean_object* v___x_550_; 
v_types_549_ = lean_ctor_get(v_d_534_, 2);
lean_inc(v_types_549_);
lean_dec_ref_known(v_d_534_, 3);
v___x_550_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_a_535_, v_types_549_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_550_;
}
default: 
{
lean_object* v_val_551_; lean_object* v_toConstantVal_552_; lean_object* v_value_553_; lean_object* v_type_554_; lean_object* v___x_555_; 
v_val_551_ = lean_ctor_get(v_d_534_, 0);
lean_inc_ref(v_val_551_);
lean_dec(v_d_534_);
v_toConstantVal_552_ = lean_ctor_get(v_val_551_, 0);
lean_inc_ref(v_toConstantVal_552_);
v_value_553_ = lean_ctor_get(v_val_551_, 1);
lean_inc_ref(v_value_553_);
lean_dec_ref(v_val_551_);
v_type_554_ = lean_ctor_get(v_toConstantVal_552_, 2);
lean_inc_ref(v_type_554_);
lean_dec_ref(v_toConstantVal_552_);
v___x_555_ = l_Lean_Meta_collectMVars(v_type_554_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
lean_dec_ref_known(v___x_555_, 1);
v___x_556_ = l_Lean_Meta_collectMVars(v_value_553_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_556_;
}
else
{
lean_dec_ref(v_value_553_);
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_534_ = stack[0].m_obj;
lean_object* v_a_535_ = stack[1].m_obj;
lean_object* v___y_536_ = stack[2].m_obj;
lean_object* v___y_537_ = stack[3].m_obj;
lean_object* v___y_538_ = stack[4].m_obj;
lean_object* v___y_539_ = stack[5].m_obj;
lean_object* v___y_540_ = stack[6].m_obj;
lean_object* v_res_557_;
v_res_557_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_534_, v_a_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(lean_object* v_d_558_, lean_object* v_a_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_558_, v_a_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
return v_res_566_;
}
}
lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object* v_d_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(0);
v___x_575_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_567_, v___x_574_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v___x_575_;
}
}
LEAN_EXPORT void l_Lean_Meta_collectMVarsAtDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_567_ = stack[0].m_obj;
lean_object* v_a_568_ = stack[1].m_obj;
lean_object* v_a_569_ = stack[2].m_obj;
lean_object* v_a_570_ = stack[3].m_obj;
lean_object* v_a_571_ = stack[4].m_obj;
lean_object* v_a_572_ = stack[5].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_Lean_Meta_collectMVarsAtDecl(v_d_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object* v_d_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Meta_collectMVarsAtDecl(v_d_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
return v_res_584_;
}
}
lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object* v_d_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_592_ = lean_st_mk_ref(v___x_591_);
v___x_593_ = l_Lean_Meta_collectMVarsAtDecl(v_d_585_, v___x_592_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_602_; 
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_603_);
v___x_595_ = v___x_593_;
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
else
{
lean_dec(v___x_593_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_result_598_; lean_object* v___x_600_; 
v___x_597_ = lean_st_ref_get(v___x_592_);
lean_dec(v___x_592_);
v_result_598_ = lean_ctor_get(v___x_597_, 1);
lean_inc_ref(v_result_598_);
lean_dec(v___x_597_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_result_598_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_result_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v___x_592_);
v_a_604_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_593_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_593_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getMVarsAtDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_585_ = stack[0].m_obj;
lean_object* v_a_586_ = stack[1].m_obj;
lean_object* v_a_587_ = stack[2].m_obj;
lean_object* v_a_588_ = stack[3].m_obj;
lean_object* v_a_589_ = stack[4].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_Lean_Meta_getMVarsAtDecl(v_d_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object* v_d_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Meta_getMVarsAtDecl(v_d_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_619_;
}
}
lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(lean_object* v_mvarId_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; lean_object* v_mctx_624_; lean_object* v_dAssignment_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_623_ = lean_st_ref_get(v___y_621_);
v_mctx_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_mctx_624_);
lean_dec(v___x_623_);
v_dAssignment_625_ = lean_ctor_get(v_mctx_624_, 9);
lean_inc_ref(v_dAssignment_625_);
lean_dec_ref(v_mctx_624_);
v___x_626_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_625_, v_mvarId_620_);
lean_dec_ref(v_dAssignment_625_);
v___x_627_ = lean_box(v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_620_ = stack[0].m_obj;
lean_object* v___y_621_ = stack[1].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_620_, v___y_621_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(lean_object* v_mvarId_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec(v_mvarId_630_);
return v_res_633_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
uint8_t v___x_636_; 
v___x_636_ = 0;
return v___x_636_;
}
else
{
lean_object* v_key_637_; lean_object* v_tail_638_; uint8_t v___x_639_; 
v_key_637_ = lean_ctor_get(v_x_635_, 0);
v_tail_638_ = lean_ctor_get(v_x_635_, 2);
v___x_639_ = l_Lean_instBEqMVarId_beq(v_key_637_, v_a_634_);
if (v___x_639_ == 0)
{
v_x_635_ = v_tail_638_;
goto _start;
}
else
{
return v___x_639_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_634_ = stack[0].m_obj;
lean_object* v_x_635_ = stack[1].m_obj;
uint8_t v_res_641_;
v_res_641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_634_, v_x_635_);
stack->m_num = v_res_641_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_642_, lean_object* v_x_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_642_, v_x_643_);
lean_dec(v_x_643_);
lean_dec(v_a_642_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_647_) == 0)
{
return v_x_646_;
}
else
{
lean_object* v_key_648_; lean_object* v_value_649_; lean_object* v_tail_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_673_; 
v_key_648_ = lean_ctor_get(v_x_647_, 0);
v_value_649_ = lean_ctor_get(v_x_647_, 1);
v_tail_650_ = lean_ctor_get(v_x_647_, 2);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_647_);
if (v_isSharedCheck_673_ == 0)
{
v___x_652_ = v_x_647_;
v_isShared_653_ = v_isSharedCheck_673_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_tail_650_);
lean_inc(v_value_649_);
lean_inc(v_key_648_);
lean_dec(v_x_647_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_673_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v_fold_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_654_ = lean_array_get_size(v_x_646_);
v___x_655_ = l_Lean_instHashableMVarId_hash(v_key_648_);
v___x_656_ = 32ULL;
v___x_657_ = lean_uint64_shift_right(v___x_655_, v___x_656_);
v_fold_658_ = lean_uint64_xor(v___x_655_, v___x_657_);
v___x_659_ = 16ULL;
v___x_660_ = lean_uint64_shift_right(v_fold_658_, v___x_659_);
v___x_661_ = lean_uint64_xor(v_fold_658_, v___x_660_);
v___x_662_ = lean_uint64_to_usize(v___x_661_);
v___x_663_ = lean_usize_of_nat(v___x_654_);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_sub(v___x_663_, v___x_664_);
v___x_666_ = lean_usize_land(v___x_662_, v___x_665_);
v___x_667_ = lean_array_uget_borrowed(v_x_646_, v___x_666_);
lean_inc(v___x_667_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 2, v___x_667_);
v___x_669_ = v___x_652_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_key_648_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_value_649_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v___x_667_);
v___x_669_ = v_reuseFailAlloc_672_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_array_uset(v_x_646_, v___x_666_, v___x_669_);
v_x_646_ = v___x_670_;
v_x_647_ = v_tail_650_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(lean_object* v_i_674_, lean_object* v_source_675_, lean_object* v_target_676_){
_start:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = lean_array_get_size(v_source_675_);
v___x_678_ = lean_nat_dec_lt(v_i_674_, v___x_677_);
if (v___x_678_ == 0)
{
lean_dec_ref(v_source_675_);
lean_dec(v_i_674_);
return v_target_676_;
}
else
{
lean_object* v_es_679_; lean_object* v___x_680_; lean_object* v_source_681_; lean_object* v_target_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_es_679_ = lean_array_fget(v_source_675_, v_i_674_);
v___x_680_ = lean_box(0);
v_source_681_ = lean_array_fset(v_source_675_, v_i_674_, v___x_680_);
v_target_682_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_target_676_, v_es_679_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_add(v_i_674_, v___x_683_);
lean_dec(v_i_674_);
v_i_674_ = v___x_684_;
v_source_675_ = v_source_681_;
v_target_676_ = v_target_682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(lean_object* v_data_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_nbuckets_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_687_ = lean_array_get_size(v_data_686_);
v___x_688_ = lean_unsigned_to_nat(2u);
v_nbuckets_689_ = lean_nat_mul(v___x_687_, v___x_688_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_box(0);
v___x_692_ = lean_mk_array(v_nbuckets_689_, v___x_691_);
v___x_693_ = lean_array_propagate_mark(v_data_686_, v___x_692_);
v___x_694_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v___x_690_, v_data_686_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(lean_object* v_m_695_, lean_object* v_a_696_, lean_object* v_b_697_){
_start:
{
lean_object* v_size_698_; lean_object* v_buckets_699_; lean_object* v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v_fold_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v_bkt_713_; uint8_t v___x_714_; 
v_size_698_ = lean_ctor_get(v_m_695_, 0);
v_buckets_699_ = lean_ctor_get(v_m_695_, 1);
v___x_700_ = lean_array_get_size(v_buckets_699_);
v___x_701_ = l_Lean_instHashableMVarId_hash(v_a_696_);
v___x_702_ = 32ULL;
v___x_703_ = lean_uint64_shift_right(v___x_701_, v___x_702_);
v_fold_704_ = lean_uint64_xor(v___x_701_, v___x_703_);
v___x_705_ = 16ULL;
v___x_706_ = lean_uint64_shift_right(v_fold_704_, v___x_705_);
v___x_707_ = lean_uint64_xor(v_fold_704_, v___x_706_);
v___x_708_ = lean_uint64_to_usize(v___x_707_);
v___x_709_ = lean_usize_of_nat(v___x_700_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_sub(v___x_709_, v___x_710_);
v___x_712_ = lean_usize_land(v___x_708_, v___x_711_);
v_bkt_713_ = lean_array_uget_borrowed(v_buckets_699_, v___x_712_);
v___x_714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_696_, v_bkt_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_735_; 
lean_inc_ref(v_buckets_699_);
lean_inc(v_size_698_);
v_isSharedCheck_735_ = !lean_is_exclusive(v_m_695_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; lean_object* v_unused_737_; 
v_unused_736_ = lean_ctor_get(v_m_695_, 1);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_m_695_, 0);
lean_dec(v_unused_737_);
v___x_716_ = v_m_695_;
v_isShared_717_ = v_isSharedCheck_735_;
goto v_resetjp_715_;
}
else
{
lean_dec(v_m_695_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_735_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v_size_x27_719_; lean_object* v___x_720_; lean_object* v_buckets_x27_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v_size_x27_719_ = lean_nat_add(v_size_698_, v___x_718_);
lean_dec(v_size_698_);
lean_inc(v_bkt_713_);
v___x_720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_720_, 0, v_a_696_);
lean_ctor_set(v___x_720_, 1, v_b_697_);
lean_ctor_set(v___x_720_, 2, v_bkt_713_);
v_buckets_x27_721_ = lean_array_uset(v_buckets_699_, v___x_712_, v___x_720_);
v___x_722_ = lean_unsigned_to_nat(4u);
v___x_723_ = lean_nat_mul(v_size_x27_719_, v___x_722_);
v___x_724_ = lean_unsigned_to_nat(3u);
v___x_725_ = lean_nat_div(v___x_723_, v___x_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_array_get_size(v_buckets_x27_721_);
v___x_727_ = lean_nat_dec_le(v___x_725_, v___x_726_);
lean_dec(v___x_725_);
if (v___x_727_ == 0)
{
lean_object* v_val_728_; lean_object* v___x_730_; 
v_val_728_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_buckets_x27_721_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_val_728_);
lean_ctor_set(v___x_716_, 0, v_size_x27_719_);
v___x_730_ = v___x_716_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_size_x27_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_val_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_object* v___x_733_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_buckets_x27_721_);
lean_ctor_set(v___x_716_, 0, v_size_x27_719_);
v___x_733_ = v___x_716_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_size_x27_719_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_buckets_x27_721_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_dec(v_b_697_);
lean_dec(v_a_696_);
return v_m_695_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(uint8_t v_includeDelayed_738_, lean_object* v_as_739_, size_t v_sz_740_, size_t v_i_741_, lean_object* v_b_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_a_750_; uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_lt(v_i_741_, v_sz_740_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v_b_742_);
return v___x_755_;
}
else
{
lean_object* v_a_756_; 
v_a_756_ = lean_array_uget_borrowed(v_as_739_, v_i_741_);
if (v_includeDelayed_738_ == 0)
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_a_756_, v___y_745_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; uint8_t v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = lean_unbox(v_a_761_);
lean_dec(v_a_761_);
if (v___x_762_ == 0)
{
goto v___jp_757_;
}
else
{
v_a_750_ = v_b_742_;
goto v___jp_749_;
}
}
else
{
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_763_; uint8_t v___x_764_; 
v_a_763_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_760_, 1);
v___x_764_ = lean_unbox(v_a_763_);
lean_dec(v_a_763_);
if (v___x_764_ == 0)
{
v_a_750_ = v_b_742_;
goto v___jp_749_;
}
else
{
goto v___jp_757_;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v_b_742_);
v_a_765_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_760_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_760_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
else
{
goto v___jp_757_;
}
v___jp_757_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_box(0);
lean_inc(v_a_756_);
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_b_742_, v_a_756_, v___x_758_);
v_a_750_ = v___x_759_;
goto v___jp_749_;
}
}
v___jp_749_:
{
size_t v___x_751_; size_t v___x_752_; 
v___x_751_ = ((size_t)1ULL);
v___x_752_ = lean_usize_add(v_i_741_, v___x_751_);
v_i_741_ = v___x_752_;
v_b_742_ = v_a_750_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeDelayed_738_ = stack[0].m_num;
lean_object* v_as_739_ = stack[1].m_obj;
size_t v_sz_740_ = stack[2].m_num;
size_t v_i_741_ = stack[3].m_num;
lean_object* v_b_742_ = stack[4].m_obj;
lean_object* v___y_743_ = stack[5].m_obj;
lean_object* v___y_744_ = stack[6].m_obj;
lean_object* v___y_745_ = stack[7].m_obj;
lean_object* v___y_746_ = stack[8].m_obj;
lean_object* v___y_747_ = stack[9].m_obj;
lean_object* v_res_773_;
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_738_, v_as_739_, v_sz_740_, v_i_741_, v_b_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___boxed(lean_object* v_includeDelayed_774_, lean_object* v_as_775_, lean_object* v_sz_776_, lean_object* v_i_777_, lean_object* v_b_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v_includeDelayed_boxed_785_; size_t v_sz_boxed_786_; size_t v_i_boxed_787_; lean_object* v_res_788_; 
v_includeDelayed_boxed_785_ = lean_unbox(v_includeDelayed_774_);
v_sz_boxed_786_ = lean_unbox_usize(v_sz_776_);
lean_dec(v_sz_776_);
v_i_boxed_787_ = lean_unbox_usize(v_i_777_);
lean_dec(v_i_777_);
v_res_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_boxed_785_, v_as_775_, v_sz_boxed_786_, v_i_boxed_787_, v_b_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v_as_775_);
return v_res_788_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = l_Lean_maxRecDepthErrorMessage;
v___x_795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3);
v___x_797_ = l_Lean_MessageData_ofFormat(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4);
v___x_799_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2));
v___x_800_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___x_798_);
return v___x_800_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(lean_object* v_ref_801_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_ref_801_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_801_ = stack[0].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_801_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(lean_object* v_ref_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_807_);
return v_res_809_;
}
}
lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(lean_object* v_mvarId_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v_mctx_814_; lean_object* v_eAssignment_815_; lean_object* v_dAssignment_816_; uint8_t v___x_817_; 
v___x_813_ = lean_st_ref_get(v___y_811_);
v_mctx_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc_ref(v_mctx_814_);
lean_dec(v___x_813_);
v_eAssignment_815_ = lean_ctor_get(v_mctx_814_, 8);
lean_inc_ref(v_eAssignment_815_);
v_dAssignment_816_ = lean_ctor_get(v_mctx_814_, 9);
lean_inc_ref(v_dAssignment_816_);
lean_dec_ref(v_mctx_814_);
v___x_817_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_eAssignment_815_, v_mvarId_810_);
lean_dec_ref(v_eAssignment_815_);
if (v___x_817_ == 0)
{
uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_816_, v_mvarId_810_);
lean_dec_ref(v_dAssignment_816_);
v___x_819_ = lean_box(v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref(v_dAssignment_816_);
v___x_821_ = lean_box(v___x_817_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_810_ = stack[0].m_obj;
lean_object* v___y_811_ = stack[1].m_obj;
lean_object* v_res_823_;
v_res_823_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_810_, v___y_811_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(lean_object* v_mvarId_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec(v_mvarId_824_);
return v_res_827_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(lean_object* v_mvarId_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_mctx_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_831_ = lean_st_ref_get(v___y_829_);
v_mctx_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_mctx_832_);
lean_dec(v___x_831_);
v___x_833_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_832_, v_mvarId_828_);
lean_dec_ref(v_mctx_832_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_828_ = stack[0].m_obj;
lean_object* v___y_829_ = stack[1].m_obj;
lean_object* v_res_835_;
v_res_835_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_828_, v___y_829_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg___boxed(lean_object* v_mvarId_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec(v_mvarId_836_);
return v_res_839_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_box(0);
v___x_841_ = lean_unsigned_to_nat(16u);
v___x_842_ = lean_mk_array(v___x_841_, v___x_840_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0);
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_843_);
return v___x_845_;
}
}
lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars(lean_object* v_e_846_, uint8_t v_includeDelayed_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_getMVars(v_e_846_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; size_t v_sz_860_; size_t v___x_861_; lean_object* v___x_862_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = lean_st_ref_get(v_a_848_);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_859_ = lean_st_ref_swap(v_a_848_, v___x_858_);
lean_dec(v___x_859_);
v_sz_860_ = lean_array_size(v_a_855_);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_847_, v_a_855_, v_sz_860_, v___x_861_, v___x_856_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_882_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_882_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_867_ = lean_st_ref_swap(v_a_848_, v_a_863_);
lean_dec(v___x_867_);
v___x_868_ = lean_array_get_size(v_a_855_);
v___x_869_ = lean_box(0);
v___x_870_ = lean_nat_dec_lt(v___x_857_, v___x_868_);
if (v___x_870_ == 0)
{
lean_object* v___x_872_; 
lean_dec(v_a_855_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_869_);
v___x_872_ = v___x_865_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_869_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
else
{
uint8_t v___x_874_; 
v___x_874_ = lean_nat_dec_le(v___x_868_, v___x_868_);
if (v___x_874_ == 0)
{
if (v___x_870_ == 0)
{
lean_object* v___x_876_; 
lean_dec(v_a_855_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_869_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_869_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
size_t v___x_878_; lean_object* v___x_879_; 
lean_del_object(v___x_865_);
v___x_878_ = lean_usize_of_nat(v___x_868_);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_855_, v___x_861_, v___x_878_, v___x_869_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_855_);
return v___x_879_;
}
}
else
{
size_t v___x_880_; lean_object* v___x_881_; 
lean_del_object(v___x_865_);
v___x_880_ = lean_usize_of_nat(v___x_868_);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_855_, v___x_861_, v___x_880_, v___x_869_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_855_);
return v___x_881_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v_a_855_);
v_a_883_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_862_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_862_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
v_a_891_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_854_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_854_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CollectMVars_0__addMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_846_ = stack[0].m_obj;
uint8_t v_includeDelayed_847_ = stack[1].m_num;
lean_object* v_a_848_ = stack[2].m_obj;
lean_object* v_a_849_ = stack[3].m_obj;
lean_object* v_a_850_ = stack[4].m_obj;
lean_object* v_a_851_ = stack[5].m_obj;
lean_object* v_a_852_ = stack[6].m_obj;
lean_object* v_res_899_;
v_res_899_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_846_, v_includeDelayed_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
stack->m_obj
 = v_res_899_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(lean_object* v_init_900_, uint8_t v_includeDelayed_901_, lean_object* v_as_902_, size_t v_sz_903_, size_t v_i_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_lt(v_i_904_, v_sz_903_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v_b_905_);
return v___x_913_;
}
else
{
lean_object* v_snd_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_948_; 
v_snd_914_ = lean_ctor_get(v_b_905_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_b_905_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_b_905_, 0);
lean_dec(v_unused_949_);
v___x_916_ = v_b_905_;
v_isShared_917_ = v_isSharedCheck_948_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_snd_914_);
lean_dec(v_b_905_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_948_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v_a_919_; lean_object* v___x_920_; 
v___x_918_ = lean_box(0);
v_a_919_ = lean_array_uget_borrowed(v_as_902_, v_i_904_);
lean_inc(v_snd_914_);
v___x_920_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_900_, v_includeDelayed_901_, v_a_919_, v_snd_914_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_939_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_939_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
if (lean_obj_tag(v_a_921_) == 0)
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_a_921_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_925_);
v___x_927_ = v___x_916_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_snd_914_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_927_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; 
lean_del_object(v___x_923_);
lean_dec(v_snd_914_);
v_a_932_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v_a_921_, 1);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v_a_932_);
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_934_ = v___x_916_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_a_932_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_904_, v___x_935_);
v_i_904_ = v___x_936_;
v_b_905_ = v___x_934_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_del_object(v___x_916_);
lean_dec(v_snd_914_);
v_a_940_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_920_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_920_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_900_ = stack[0].m_obj;
uint8_t v_includeDelayed_901_ = stack[1].m_num;
lean_object* v_as_902_ = stack[2].m_obj;
size_t v_sz_903_ = stack[3].m_num;
size_t v_i_904_ = stack[4].m_num;
lean_object* v_b_905_ = stack[5].m_obj;
lean_object* v___y_906_ = stack[6].m_obj;
lean_object* v___y_907_ = stack[7].m_obj;
lean_object* v___y_908_ = stack[8].m_obj;
lean_object* v___y_909_ = stack[9].m_obj;
lean_object* v___y_910_ = stack[10].m_obj;
lean_object* v_res_950_;
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_900_, v_includeDelayed_901_, v_as_902_, v_sz_903_, v_i_904_, v_b_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
stack->m_obj
 = v_res_950_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(uint8_t v_includeDelayed_951_, lean_object* v_as_952_, size_t v_sz_953_, size_t v_i_954_, lean_object* v_b_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_lt(v_i_954_, v_sz_953_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_b_955_);
return v___x_963_;
}
else
{
lean_object* v_snd_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1002_; 
v_snd_964_ = lean_ctor_get(v_b_955_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_b_955_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v_b_955_, 0);
lean_dec(v_unused_1003_);
v___x_966_ = v_b_955_;
v_isShared_967_ = v_isSharedCheck_1002_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_snd_964_);
lean_dec(v_b_955_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1002_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v_a_970_; lean_object* v_a_977_; 
v___x_968_ = lean_box(0);
v_a_977_ = lean_array_uget_borrowed(v_as_952_, v_i_954_);
if (lean_obj_tag(v_a_977_) == 0)
{
v_a_970_ = v_snd_964_;
goto v___jp_969_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec(v_snd_964_);
v_val_978_ = lean_ctor_get(v_a_977_, 0);
v___x_979_ = lean_box(0);
v___x_980_ = l_Lean_LocalDecl_type(v_val_978_);
v___x_981_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_980_, v_includeDelayed_951_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_981_) == 0)
{
uint8_t v___x_982_; lean_object* v___x_983_; 
lean_dec_ref_known(v___x_981_, 1);
v___x_982_ = 0;
v___x_983_ = l_Lean_LocalDecl_value_x3f(v_val_978_, v___x_982_);
if (lean_obj_tag(v___x_983_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_985_; 
v_val_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_984_, v_includeDelayed_951_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_dec_ref_known(v___x_985_, 1);
v_a_970_ = v___x_979_;
goto v___jp_969_;
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_del_object(v___x_966_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_dec(v___x_983_);
v_a_970_ = v___x_979_;
goto v___jp_969_;
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_del_object(v___x_966_);
v_a_994_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_981_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_981_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
v___jp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v_a_970_);
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_972_ = v___x_966_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_a_970_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
size_t v___x_973_; size_t v___x_974_; 
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_954_, v___x_973_);
v_i_954_ = v___x_974_;
v_b_955_ = v___x_972_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeDelayed_951_ = stack[0].m_num;
lean_object* v_as_952_ = stack[1].m_obj;
size_t v_sz_953_ = stack[2].m_num;
size_t v_i_954_ = stack[3].m_num;
lean_object* v_b_955_ = stack[4].m_obj;
lean_object* v___y_956_ = stack[5].m_obj;
lean_object* v___y_957_ = stack[6].m_obj;
lean_object* v___y_958_ = stack[7].m_obj;
lean_object* v___y_959_ = stack[8].m_obj;
lean_object* v___y_960_ = stack[9].m_obj;
lean_object* v_res_1004_;
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_951_, v_as_952_, v_sz_953_, v_i_954_, v_b_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
stack->m_obj
 = v_res_1004_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(uint8_t v_includeDelayed_1005_, lean_object* v_as_1006_, size_t v_sz_1007_, size_t v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_usize_dec_lt(v_i_1008_, v_sz_1007_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_b_1009_);
return v___x_1017_;
}
else
{
lean_object* v_snd_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1056_; 
v_snd_1018_ = lean_ctor_get(v_b_1009_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_b_1009_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v_b_1009_, 0);
lean_dec(v_unused_1057_);
v___x_1020_ = v_b_1009_;
v_isShared_1021_ = v_isSharedCheck_1056_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snd_1018_);
lean_dec(v_b_1009_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1056_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v_a_1024_; lean_object* v_a_1031_; 
v___x_1022_ = lean_box(0);
v_a_1031_ = lean_array_uget_borrowed(v_as_1006_, v_i_1008_);
if (lean_obj_tag(v_a_1031_) == 0)
{
v_a_1024_ = v_snd_1018_;
goto v___jp_1023_;
}
else
{
lean_object* v_val_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec(v_snd_1018_);
v_val_1032_ = lean_ctor_get(v_a_1031_, 0);
v___x_1033_ = lean_box(0);
v___x_1034_ = l_Lean_LocalDecl_type(v_val_1032_);
v___x_1035_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1034_, v_includeDelayed_1005_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1035_) == 0)
{
uint8_t v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref_known(v___x_1035_, 1);
v___x_1036_ = 0;
v___x_1037_ = l_Lean_LocalDecl_value_x3f(v_val_1032_, v___x_1036_);
if (lean_obj_tag(v___x_1037_) == 1)
{
lean_object* v_val_1038_; lean_object* v___x_1039_; 
v_val_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1038_, v_includeDelayed_1005_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_dec_ref_known(v___x_1039_, 1);
v_a_1024_ = v___x_1033_;
goto v___jp_1023_;
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_del_object(v___x_1020_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_dec(v___x_1037_);
v_a_1024_ = v___x_1033_;
goto v___jp_1023_;
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_del_object(v___x_1020_);
v_a_1048_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1035_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1035_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
v___jp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v_a_1024_);
lean_ctor_set(v___x_1020_, 0, v___x_1022_);
v___x_1026_ = v___x_1020_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_a_1024_);
v___x_1026_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = lean_usize_add(v_i_1008_, v___x_1027_);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_1005_, v_as_1006_, v_sz_1007_, v___x_1028_, v___x_1026_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
return v___x_1029_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeDelayed_1005_ = stack[0].m_num;
lean_object* v_as_1006_ = stack[1].m_obj;
size_t v_sz_1007_ = stack[2].m_num;
size_t v_i_1008_ = stack[3].m_num;
lean_object* v_b_1009_ = stack[4].m_obj;
lean_object* v___y_1010_ = stack[5].m_obj;
lean_object* v___y_1011_ = stack[6].m_obj;
lean_object* v___y_1012_ = stack[7].m_obj;
lean_object* v___y_1013_ = stack[8].m_obj;
lean_object* v___y_1014_ = stack[9].m_obj;
lean_object* v_res_1058_;
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_1005_, v_as_1006_, v_sz_1007_, v_i_1008_, v_b_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
stack->m_obj
 = v_res_1058_;
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(lean_object* v_init_1059_, uint8_t v_includeDelayed_1060_, lean_object* v_n_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
if (lean_obj_tag(v_n_1061_) == 0)
{
lean_object* v_cs_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; size_t v_sz_1072_; size_t v___x_1073_; lean_object* v___x_1074_; 
v_cs_1069_ = lean_ctor_get(v_n_1061_, 0);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_b_1062_);
v_sz_1072_ = lean_array_size(v_cs_1069_);
v___x_1073_ = ((size_t)0ULL);
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_1059_, v_includeDelayed_1060_, v_cs_1069_, v_sz_1072_, v___x_1073_, v___x_1071_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1089_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1089_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1089_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_fst_1079_; 
v_fst_1079_ = lean_ctor_get(v_a_1075_, 0);
if (lean_obj_tag(v_fst_1079_) == 0)
{
lean_object* v_snd_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v_snd_1080_ = lean_ctor_get(v_a_1075_, 1);
lean_inc(v_snd_1080_);
lean_dec(v_a_1075_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_snd_1080_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1081_);
v___x_1083_ = v___x_1077_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
else
{
lean_object* v_val_1085_; lean_object* v___x_1087_; 
lean_inc_ref(v_fst_1079_);
lean_dec(v_a_1075_);
v_val_1085_ = lean_ctor_get(v_fst_1079_, 0);
lean_inc(v_val_1085_);
lean_dec_ref_known(v_fst_1079_, 1);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v_val_1085_);
v___x_1087_ = v___x_1077_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_val_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1074_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1074_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_vs_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v_vs_1098_ = lean_ctor_get(v_n_1061_, 0);
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v_b_1062_);
v_sz_1101_ = lean_array_size(v_vs_1098_);
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_1060_, v_vs_1098_, v_sz_1101_, v___x_1102_, v___x_1100_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1118_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1118_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1118_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_fst_1108_; 
v_fst_1108_ = lean_ctor_get(v_a_1104_, 0);
if (lean_obj_tag(v_fst_1108_) == 0)
{
lean_object* v_snd_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v_snd_1109_ = lean_ctor_get(v_a_1104_, 1);
lean_inc(v_snd_1109_);
lean_dec(v_a_1104_);
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_snd_1109_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1110_);
v___x_1112_ = v___x_1106_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
lean_object* v_val_1114_; lean_object* v___x_1116_; 
lean_inc_ref(v_fst_1108_);
lean_dec(v_a_1104_);
v_val_1114_ = lean_ctor_get(v_fst_1108_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v_fst_1108_, 1);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v_val_1114_);
v___x_1116_ = v___x_1106_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_val_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1119_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1103_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1103_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1059_ = stack[0].m_obj;
uint8_t v_includeDelayed_1060_ = stack[1].m_num;
lean_object* v_n_1061_ = stack[2].m_obj;
lean_object* v_b_1062_ = stack[3].m_obj;
lean_object* v___y_1063_ = stack[4].m_obj;
lean_object* v___y_1064_ = stack[5].m_obj;
lean_object* v___y_1065_ = stack[6].m_obj;
lean_object* v___y_1066_ = stack[7].m_obj;
lean_object* v___y_1067_ = stack[8].m_obj;
lean_object* v_res_1127_;
v_res_1127_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1059_, v_includeDelayed_1060_, v_n_1061_, v_b_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
stack->m_obj
 = v_res_1127_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(uint8_t v_includeDelayed_1128_, lean_object* v_as_1129_, size_t v_sz_1130_, size_t v_i_1131_, lean_object* v_b_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_usize_dec_lt(v_i_1131_, v_sz_1130_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_b_1132_);
return v___x_1140_;
}
else
{
lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1179_; 
v_snd_1141_ = lean_ctor_get(v_b_1132_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_b_1132_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v_b_1132_, 0);
lean_dec(v_unused_1180_);
v___x_1143_ = v_b_1132_;
v_isShared_1144_ = v_isSharedCheck_1179_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_dec(v_b_1132_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1179_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v_a_1147_; lean_object* v_a_1154_; 
v___x_1145_ = lean_box(0);
v_a_1154_ = lean_array_uget_borrowed(v_as_1129_, v_i_1131_);
if (lean_obj_tag(v_a_1154_) == 0)
{
v_a_1147_ = v_snd_1141_;
goto v___jp_1146_;
}
else
{
lean_object* v_val_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_snd_1141_);
v_val_1155_ = lean_ctor_get(v_a_1154_, 0);
v___x_1156_ = lean_box(0);
v___x_1157_ = l_Lean_LocalDecl_type(v_val_1155_);
v___x_1158_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1157_, v_includeDelayed_1128_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1158_) == 0)
{
uint8_t v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref_known(v___x_1158_, 1);
v___x_1159_ = 0;
v___x_1160_ = l_Lean_LocalDecl_value_x3f(v_val_1155_, v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 1)
{
lean_object* v_val_1161_; lean_object* v___x_1162_; 
v_val_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_val_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1162_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1161_, v_includeDelayed_1128_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_dec_ref_known(v___x_1162_, 1);
v_a_1147_ = v___x_1156_;
goto v___jp_1146_;
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_del_object(v___x_1143_);
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_dec(v___x_1160_);
v_a_1147_ = v___x_1156_;
goto v___jp_1146_;
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_del_object(v___x_1143_);
v_a_1171_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1158_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1158_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
v___jp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_a_1147_);
lean_ctor_set(v___x_1143_, 0, v___x_1145_);
v___x_1149_ = v___x_1143_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_a_1147_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
size_t v___x_1150_; size_t v___x_1151_; 
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_add(v_i_1131_, v___x_1150_);
v_i_1131_ = v___x_1151_;
v_b_1132_ = v___x_1149_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeDelayed_1128_ = stack[0].m_num;
lean_object* v_as_1129_ = stack[1].m_obj;
size_t v_sz_1130_ = stack[2].m_num;
size_t v_i_1131_ = stack[3].m_num;
lean_object* v_b_1132_ = stack[4].m_obj;
lean_object* v___y_1133_ = stack[5].m_obj;
lean_object* v___y_1134_ = stack[6].m_obj;
lean_object* v___y_1135_ = stack[7].m_obj;
lean_object* v___y_1136_ = stack[8].m_obj;
lean_object* v___y_1137_ = stack[9].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_1128_, v_as_1129_, v_sz_1130_, v_i_1131_, v_b_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
stack->m_obj
 = v_res_1181_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(uint8_t v_includeDelayed_1182_, lean_object* v_as_1183_, size_t v_sz_1184_, size_t v_i_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_usize_dec_lt(v_i_1185_, v_sz_1184_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_b_1186_);
return v___x_1194_;
}
else
{
lean_object* v_snd_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1233_; 
v_snd_1195_ = lean_ctor_get(v_b_1186_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_b_1186_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_b_1186_, 0);
lean_dec(v_unused_1234_);
v___x_1197_ = v_b_1186_;
v_isShared_1198_ = v_isSharedCheck_1233_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_snd_1195_);
lean_dec(v_b_1186_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1233_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v_a_1201_; lean_object* v_a_1208_; 
v___x_1199_ = lean_box(0);
v_a_1208_ = lean_array_uget_borrowed(v_as_1183_, v_i_1185_);
if (lean_obj_tag(v_a_1208_) == 0)
{
v_a_1201_ = v_snd_1195_;
goto v___jp_1200_;
}
else
{
lean_object* v_val_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec(v_snd_1195_);
v_val_1209_ = lean_ctor_get(v_a_1208_, 0);
v___x_1210_ = lean_box(0);
v___x_1211_ = l_Lean_LocalDecl_type(v_val_1209_);
v___x_1212_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1211_, v_includeDelayed_1182_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1212_) == 0)
{
uint8_t v___x_1213_; lean_object* v___x_1214_; 
lean_dec_ref_known(v___x_1212_, 1);
v___x_1213_ = 0;
v___x_1214_ = l_Lean_LocalDecl_value_x3f(v_val_1209_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1216_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1215_, v_includeDelayed_1182_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_dec_ref_known(v___x_1216_, 1);
v_a_1201_ = v___x_1210_;
goto v___jp_1200_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_del_object(v___x_1197_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
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
else
{
lean_dec(v___x_1214_);
v_a_1201_ = v___x_1210_;
goto v___jp_1200_;
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_del_object(v___x_1197_);
v_a_1225_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1212_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1212_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
v___jp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v_a_1201_);
lean_ctor_set(v___x_1197_, 0, v___x_1199_);
v___x_1203_ = v___x_1197_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_a_1201_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = lean_usize_add(v_i_1185_, v___x_1204_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_1182_, v_as_1183_, v_sz_1184_, v___x_1205_, v___x_1203_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1206_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeDelayed_1182_ = stack[0].m_num;
lean_object* v_as_1183_ = stack[1].m_obj;
size_t v_sz_1184_ = stack[2].m_num;
size_t v_i_1185_ = stack[3].m_num;
lean_object* v_b_1186_ = stack[4].m_obj;
lean_object* v___y_1187_ = stack[5].m_obj;
lean_object* v___y_1188_ = stack[6].m_obj;
lean_object* v___y_1189_ = stack[7].m_obj;
lean_object* v___y_1190_ = stack[8].m_obj;
lean_object* v___y_1191_ = stack[9].m_obj;
lean_object* v_res_1235_;
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_1182_, v_as_1183_, v_sz_1184_, v_i_1185_, v_b_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
stack->m_obj
 = v_res_1235_;
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(uint8_t v_includeDelayed_1236_, lean_object* v_t_1237_, lean_object* v_init_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_root_1245_; lean_object* v_tail_1246_; lean_object* v___x_1247_; 
v_root_1245_ = lean_ctor_get(v_t_1237_, 0);
v_tail_1246_ = lean_ctor_get(v_t_1237_, 1);
v___x_1247_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1238_, v_includeDelayed_1236_, v_root_1245_, v_init_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1284_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1284_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1284_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
if (lean_obj_tag(v_a_1248_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; 
v_a_1252_ = lean_ctor_get(v_a_1248_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v_a_1248_, 1);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v_a_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; size_t v_sz_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
lean_del_object(v___x_1250_);
v_a_1256_ = lean_ctor_get(v_a_1248_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v_a_1248_, 1);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_a_1256_);
v_sz_1259_ = lean_array_size(v_tail_1246_);
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_1236_, v_tail_1246_, v_sz_1259_, v___x_1260_, v___x_1258_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1275_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1275_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1275_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v_fst_1266_; 
v_fst_1266_ = lean_ctor_get(v_a_1262_, 0);
if (lean_obj_tag(v_fst_1266_) == 0)
{
lean_object* v_snd_1267_; lean_object* v___x_1269_; 
v_snd_1267_ = lean_ctor_get(v_a_1262_, 1);
lean_inc(v_snd_1267_);
lean_dec(v_a_1262_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_snd_1267_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_snd_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
else
{
lean_object* v_val_1271_; lean_object* v___x_1273_; 
lean_inc_ref(v_fst_1266_);
lean_dec(v_a_1262_);
v_val_1271_ = lean_ctor_get(v_fst_1266_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v_fst_1266_, 1);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_val_1271_);
v___x_1273_ = v___x_1264_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_val_1271_);
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
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1261_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1261_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1247_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1247_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeDelayed_1236_ = stack[0].m_num;
lean_object* v_t_1237_ = stack[1].m_obj;
lean_object* v_init_1238_ = stack[2].m_obj;
lean_object* v___y_1239_ = stack[3].m_obj;
lean_object* v___y_1240_ = stack[4].m_obj;
lean_object* v___y_1241_ = stack[5].m_obj;
lean_object* v___y_1242_ = stack[6].m_obj;
lean_object* v___y_1243_ = stack[7].m_obj;
lean_object* v_res_1293_;
v_res_1293_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_1236_, v_t_1237_, v_init_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
stack->m_obj
 = v_res_1293_;
}
lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object* v_mvarId_1294_, uint8_t v_includeDelayed_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v_toCold_1310_; lean_object* v_currRecDepth_1311_; lean_object* v_ref_1312_; uint16_t v_optionFlags_1313_; uint8_t v_suppressElabErrors_1314_; uint8_t v_isRecordingDeps_1315_; lean_object* v_maxRecDepth_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_toCold_1310_ = lean_ctor_get(v_a_1299_, 0);
lean_inc_ref(v_toCold_1310_);
v_currRecDepth_1311_ = lean_ctor_get(v_a_1299_, 1);
lean_inc(v_currRecDepth_1311_);
v_ref_1312_ = lean_ctor_get(v_a_1299_, 2);
lean_inc(v_ref_1312_);
v_optionFlags_1313_ = lean_ctor_get_uint16(v_a_1299_, sizeof(void*)*3);
v_suppressElabErrors_1314_ = lean_ctor_get_uint8(v_a_1299_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1315_ = lean_ctor_get_uint8(v_a_1299_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_1299_);
v_maxRecDepth_1370_ = lean_ctor_get(v_toCold_1310_, 3);
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_nat_dec_eq(v_maxRecDepth_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_nat_dec_eq(v_currRecDepth_1311_, v_maxRecDepth_1370_);
if (v___x_1373_ == 0)
{
goto v___jp_1316_;
}
else
{
lean_object* v___x_1374_; 
lean_dec(v_currRecDepth_1311_);
lean_dec_ref(v_toCold_1310_);
lean_dec(v_mvarId_1294_);
v___x_1374_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1312_);
return v___x_1374_;
}
}
else
{
goto v___jp_1316_;
}
v___jp_1302_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_st_ref_take(v_a_1296_);
lean_inc(v___y_1305_);
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_1306_, v___y_1305_, v___y_1304_);
v___x_1308_ = lean_st_ref_put(v_a_1296_, v___x_1307_);
v_mvarId_1294_ = v___y_1305_;
v_a_1299_ = v___y_1303_;
goto _start;
}
v___jp_1316_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = lean_nat_add(v_currRecDepth_1311_, v___x_1317_);
lean_dec(v_currRecDepth_1311_);
v___x_1319_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1319_, 0, v_toCold_1310_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
lean_ctor_set(v___x_1319_, 2, v_ref_1312_);
lean_ctor_set_uint16(v___x_1319_, sizeof(void*)*3, v_optionFlags_1313_);
lean_ctor_set_uint8(v___x_1319_, sizeof(void*)*3 + 2, v_suppressElabErrors_1314_);
lean_ctor_set_uint8(v___x_1319_, sizeof(void*)*3 + 3, v_isRecordingDeps_1315_);
lean_inc(v_mvarId_1294_);
v___x_1320_ = l_Lean_MVarId_getDecl(v_mvarId_1294_, v_a_1297_, v_a_1298_, v___x_1319_, v_a_1300_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v_lctx_1322_; lean_object* v_type_1323_; lean_object* v___x_1324_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v_lctx_1322_ = lean_ctor_get(v_a_1321_, 1);
lean_inc_ref(v_lctx_1322_);
v_type_1323_ = lean_ctor_get(v_a_1321_, 2);
lean_inc_ref(v_type_1323_);
lean_dec(v_a_1321_);
v___x_1324_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_type_1323_, v_includeDelayed_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v___x_1319_, v_a_1300_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_decls_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec_ref_known(v___x_1324_, 1);
v_decls_1325_ = lean_ctor_get(v_lctx_1322_, 1);
lean_inc_ref(v_decls_1325_);
lean_dec_ref(v_lctx_1322_);
v___x_1326_ = lean_box(0);
v___x_1327_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_1295_, v_decls_1325_, v___x_1326_, v_a_1296_, v_a_1297_, v_a_1298_, v___x_1319_, v_a_1300_);
lean_dec_ref(v_decls_1325_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v___x_1328_; 
lean_dec_ref_known(v___x_1327_, 1);
v___x_1328_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1294_, v_a_1298_);
lean_dec(v_mvarId_1294_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1353_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1353_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1353_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
if (lean_obj_tag(v_a_1329_) == 1)
{
lean_object* v_val_1333_; lean_object* v_mvarIdPending_1334_; lean_object* v___x_1335_; 
lean_del_object(v___x_1331_);
v_val_1333_ = lean_ctor_get(v_a_1329_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_a_1329_, 1);
v_mvarIdPending_1334_ = lean_ctor_get(v_val_1333_, 1);
lean_inc(v_mvarIdPending_1334_);
lean_dec(v_val_1333_);
v___x_1335_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarIdPending_1334_, v_a_1298_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; uint8_t v___x_1337_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = lean_unbox(v_a_1336_);
lean_dec(v_a_1336_);
if (v___x_1337_ == 0)
{
v___y_1303_ = v___x_1319_;
v___y_1304_ = v___x_1326_;
v___y_1305_ = v_mvarIdPending_1334_;
goto v___jp_1302_;
}
else
{
v_mvarId_1294_ = v_mvarIdPending_1334_;
v_a_1299_ = v___x_1319_;
goto _start;
}
}
else
{
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1339_; uint8_t v___x_1340_; 
v_a_1339_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1340_ = lean_unbox(v_a_1339_);
lean_dec(v_a_1339_);
if (v___x_1340_ == 0)
{
v_mvarId_1294_ = v_mvarIdPending_1334_;
v_a_1299_ = v___x_1319_;
goto _start;
}
else
{
v___y_1303_ = v___x_1319_;
v___y_1304_ = v___x_1326_;
v___y_1305_ = v_mvarIdPending_1334_;
goto v___jp_1302_;
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_mvarIdPending_1334_);
lean_dec_ref_known(v___x_1319_, 3);
v_a_1342_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1335_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1335_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
else
{
lean_object* v___x_1351_; 
lean_dec(v_a_1329_);
lean_dec_ref_known(v___x_1319_, 3);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1326_);
v___x_1351_ = v___x_1331_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1326_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref_known(v___x_1319_, 3);
v_a_1354_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1328_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1328_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1319_, 3);
lean_dec(v_mvarId_1294_);
return v___x_1327_;
}
}
else
{
lean_dec_ref(v_lctx_1322_);
lean_dec_ref_known(v___x_1319_, 3);
lean_dec(v_mvarId_1294_);
return v___x_1324_;
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref_known(v___x_1319_, 3);
lean_dec(v_mvarId_1294_);
v_a_1362_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1320_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1320_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CollectMVars_0__go_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1294_ = stack[0].m_obj;
uint8_t v_includeDelayed_1295_ = stack[1].m_num;
lean_object* v_a_1296_ = stack[2].m_obj;
lean_object* v_a_1297_ = stack[3].m_obj;
lean_object* v_a_1298_ = stack[4].m_obj;
lean_object* v_a_1299_ = stack[5].m_obj;
lean_object* v_a_1300_ = stack[6].m_obj;
lean_object* v_res_1375_;
v_res_1375_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1294_, v_includeDelayed_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
stack->m_obj
 = v_res_1375_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(lean_object* v_as_1376_, size_t v_i_1377_, size_t v_stop_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_usize_dec_eq(v_i_1377_, v_stop_1378_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_array_uget_borrowed(v_as_1376_, v_i_1377_);
lean_inc_ref(v___y_1383_);
lean_inc(v___x_1387_);
v___x_1388_ = l___private_Lean_Meta_CollectMVars_0__go(v___x_1387_, v___x_1386_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; size_t v___x_1390_; size_t v___x_1391_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = ((size_t)1ULL);
v___x_1391_ = lean_usize_add(v_i_1377_, v___x_1390_);
v_i_1377_ = v___x_1391_;
v_b_1379_ = v_a_1389_;
goto _start;
}
else
{
return v___x_1388_;
}
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_b_1379_);
return v___x_1393_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1376_ = stack[0].m_obj;
size_t v_i_1377_ = stack[1].m_num;
size_t v_stop_1378_ = stack[2].m_num;
lean_object* v_b_1379_ = stack[3].m_obj;
lean_object* v___y_1380_ = stack[4].m_obj;
lean_object* v___y_1381_ = stack[5].m_obj;
lean_object* v___y_1382_ = stack[6].m_obj;
lean_object* v___y_1383_ = stack[7].m_obj;
lean_object* v___y_1384_ = stack[8].m_obj;
lean_object* v_res_1394_;
v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_as_1376_, v_i_1377_, v_stop_1378_, v_b_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
stack->m_obj
 = v_res_1394_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object* v_as_1395_, lean_object* v_i_1396_, lean_object* v_stop_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
size_t v_i_boxed_1405_; size_t v_stop_boxed_1406_; lean_object* v_res_1407_; 
v_i_boxed_1405_ = lean_unbox_usize(v_i_1396_);
lean_dec(v_i_1396_);
v_stop_boxed_1406_ = lean_unbox_usize(v_stop_1397_);
lean_dec(v_stop_1397_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_as_1395_, v_i_boxed_1405_, v_stop_boxed_1406_, v_b_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v_as_1395_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(lean_object* v_init_1408_, lean_object* v_includeDelayed_1409_, lean_object* v_as_1410_, lean_object* v_sz_1411_, lean_object* v_i_1412_, lean_object* v_b_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v_includeDelayed_boxed_1420_; size_t v_sz_boxed_1421_; size_t v_i_boxed_1422_; lean_object* v_res_1423_; 
v_includeDelayed_boxed_1420_ = lean_unbox(v_includeDelayed_1409_);
v_sz_boxed_1421_ = lean_unbox_usize(v_sz_1411_);
lean_dec(v_sz_1411_);
v_i_boxed_1422_ = lean_unbox_usize(v_i_1412_);
lean_dec(v_i_1412_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_1408_, v_includeDelayed_boxed_1420_, v_as_1410_, v_sz_boxed_1421_, v_i_boxed_1422_, v_b_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v_as_1410_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(lean_object* v_includeDelayed_1424_, lean_object* v_t_1425_, lean_object* v_init_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_includeDelayed_boxed_1433_; lean_object* v_res_1434_; 
v_includeDelayed_boxed_1433_ = lean_unbox(v_includeDelayed_1424_);
v_res_1434_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_boxed_1433_, v_t_1425_, v_init_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v_t_1425_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object* v_includeDelayed_1435_, lean_object* v_as_1436_, lean_object* v_sz_1437_, lean_object* v_i_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v_includeDelayed_boxed_1446_; size_t v_sz_boxed_1447_; size_t v_i_boxed_1448_; lean_object* v_res_1449_; 
v_includeDelayed_boxed_1446_ = lean_unbox(v_includeDelayed_1435_);
v_sz_boxed_1447_ = lean_unbox_usize(v_sz_1437_);
lean_dec(v_sz_1437_);
v_i_boxed_1448_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_boxed_1446_, v_as_1436_, v_sz_boxed_1447_, v_i_boxed_1448_, v_b_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v_as_1436_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object* v_includeDelayed_1450_, lean_object* v_as_1451_, lean_object* v_sz_1452_, lean_object* v_i_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v_includeDelayed_boxed_1461_; size_t v_sz_boxed_1462_; size_t v_i_boxed_1463_; lean_object* v_res_1464_; 
v_includeDelayed_boxed_1461_ = lean_unbox(v_includeDelayed_1450_);
v_sz_boxed_1462_ = lean_unbox_usize(v_sz_1452_);
lean_dec(v_sz_1452_);
v_i_boxed_1463_ = lean_unbox_usize(v_i_1453_);
lean_dec(v_i_1453_);
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_boxed_1461_, v_as_1451_, v_sz_boxed_1462_, v_i_boxed_1463_, v_b_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v_as_1451_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object* v_includeDelayed_1465_, lean_object* v_as_1466_, lean_object* v_sz_1467_, lean_object* v_i_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
uint8_t v_includeDelayed_boxed_1476_; size_t v_sz_boxed_1477_; size_t v_i_boxed_1478_; lean_object* v_res_1479_; 
v_includeDelayed_boxed_1476_ = lean_unbox(v_includeDelayed_1465_);
v_sz_boxed_1477_ = lean_unbox_usize(v_sz_1467_);
lean_dec(v_sz_1467_);
v_i_boxed_1478_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_boxed_1476_, v_as_1466_, v_sz_boxed_1477_, v_i_boxed_1478_, v_b_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v_as_1466_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object* v_includeDelayed_1480_, lean_object* v_as_1481_, lean_object* v_sz_1482_, lean_object* v_i_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_includeDelayed_boxed_1491_; size_t v_sz_boxed_1492_; size_t v_i_boxed_1493_; lean_object* v_res_1494_; 
v_includeDelayed_boxed_1491_ = lean_unbox(v_includeDelayed_1480_);
v_sz_boxed_1492_ = lean_unbox_usize(v_sz_1482_);
lean_dec(v_sz_1482_);
v_i_boxed_1493_ = lean_unbox_usize(v_i_1483_);
lean_dec(v_i_1483_);
v_res_1494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_boxed_1491_, v_as_1481_, v_sz_boxed_1492_, v_i_boxed_1493_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v_as_1481_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object* v_init_1495_, lean_object* v_includeDelayed_1496_, lean_object* v_n_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v_includeDelayed_boxed_1505_; lean_object* v_res_1506_; 
v_includeDelayed_boxed_1505_ = lean_unbox(v_includeDelayed_1496_);
v_res_1506_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1495_, v_includeDelayed_boxed_1505_, v_n_1497_, v_b_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v_n_1497_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object* v_e_1507_, lean_object* v_includeDelayed_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
uint8_t v_includeDelayed_boxed_1515_; lean_object* v_res_1516_; 
v_includeDelayed_boxed_1515_ = lean_unbox(v_includeDelayed_1508_);
v_res_1516_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1507_, v_includeDelayed_boxed_1515_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go___boxed(lean_object* v_mvarId_1517_, lean_object* v_includeDelayed_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
uint8_t v_includeDelayed_boxed_1525_; lean_object* v_res_1526_; 
v_includeDelayed_boxed_1525_ = lean_unbox(v_includeDelayed_1518_);
v_res_1526_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1517_, v_includeDelayed_boxed_1525_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
lean_dec(v_a_1523_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
return v_res_1526_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(lean_object* v_mvarId_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1527_, v___y_1530_);
return v___x_1534_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1527_ = stack[0].m_obj;
lean_object* v___y_1528_ = stack[1].m_obj;
lean_object* v___y_1529_ = stack[2].m_obj;
lean_object* v___y_1530_ = stack[3].m_obj;
lean_object* v___y_1531_ = stack[4].m_obj;
lean_object* v___y_1532_ = stack[5].m_obj;
lean_object* v_res_1535_;
v_res_1535_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(v_mvarId_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
stack->m_obj
 = v_res_1535_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(lean_object* v_mvarId_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(v_mvarId_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec(v_mvarId_1536_);
return v_res_1543_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_object* v_00_u03b1_1544_, lean_object* v_ref_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1545_);
return v___x_1552_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1545_ = stack[1].m_obj;
lean_object* v___y_1546_ = stack[2].m_obj;
lean_object* v___y_1547_ = stack[3].m_obj;
lean_object* v___y_1548_ = stack[4].m_obj;
lean_object* v___y_1549_ = stack[5].m_obj;
lean_object* v___y_1550_ = stack[6].m_obj;
lean_object* v_res_1553_;
v_res_1553_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_box(0), v_ref_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
stack->m_obj
 = v_res_1553_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_ref_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(v_00_u03b1_1554_, v_ref_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(lean_object* v_00_u03b2_1563_, lean_object* v_m_1564_, lean_object* v_a_1565_, lean_object* v_b_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_1564_, v_a_1565_, v_b_1566_);
return v___x_1567_;
}
}
lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(lean_object* v_mvarId_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_1568_, v___y_1571_);
return v___x_1575_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1568_ = stack[0].m_obj;
lean_object* v___y_1569_ = stack[1].m_obj;
lean_object* v___y_1570_ = stack[2].m_obj;
lean_object* v___y_1571_ = stack[3].m_obj;
lean_object* v___y_1572_ = stack[4].m_obj;
lean_object* v___y_1573_ = stack[5].m_obj;
lean_object* v_res_1576_;
v_res_1576_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_mvarId_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
stack->m_obj
 = v_res_1576_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(lean_object* v_mvarId_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_mvarId_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec(v_mvarId_1577_);
return v_res_1584_;
}
}
lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(lean_object* v_mvarId_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_1585_, v___y_1588_);
return v___x_1592_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1585_ = stack[0].m_obj;
lean_object* v___y_1586_ = stack[1].m_obj;
lean_object* v___y_1587_ = stack[2].m_obj;
lean_object* v___y_1588_ = stack[3].m_obj;
lean_object* v___y_1589_ = stack[4].m_obj;
lean_object* v___y_1590_ = stack[5].m_obj;
lean_object* v_res_1593_;
v_res_1593_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
stack->m_obj
 = v_res_1593_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(lean_object* v_mvarId_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec(v_mvarId_1594_);
return v_res_1601_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_object* v_00_u03b2_1602_, lean_object* v_a_1603_, lean_object* v_x_1604_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_1603_, v_x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1603_ = stack[1].m_obj;
lean_object* v_x_1604_ = stack[2].m_obj;
uint8_t v_res_1606_;
v_res_1606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_box(0), v_a_1603_, v_x_1604_);
stack->m_num = v_res_1606_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1607_, lean_object* v_a_1608_, lean_object* v_x_1609_){
_start:
{
uint8_t v_res_1610_; lean_object* v_r_1611_; 
v_res_1610_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(v_00_u03b2_1607_, v_a_1608_, v_x_1609_);
lean_dec(v_x_1609_);
lean_dec(v_a_1608_);
v_r_1611_ = lean_box(v_res_1610_);
return v_r_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1(lean_object* v_00_u03b2_1612_, lean_object* v_data_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_data_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1615_, lean_object* v_i_1616_, lean_object* v_source_1617_, lean_object* v_target_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v_i_1616_, v_source_1617_, v_target_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_x_1621_, v_x_1622_);
return v___x_1623_;
}
}
lean_object* l_Lean_MVarId_getMVarDependencies(lean_object* v_mvarId_1624_, uint8_t v_includeDelayed_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1632_ = lean_st_mk_ref(v___x_1631_);
lean_inc_ref(v_a_1628_);
v___x_1633_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1624_, v_includeDelayed_1625_, v___x_1632_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1641_; 
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v___x_1633_, 0);
lean_dec(v_unused_1642_);
v___x_1635_ = v___x_1633_;
v_isShared_1636_ = v_isSharedCheck_1641_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v___x_1633_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1641_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = lean_st_ref_get(v___x_1632_);
lean_dec(v___x_1632_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v___x_1632_);
v_a_1643_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1633_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1633_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_getMVarDependencies_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1624_ = stack[0].m_obj;
uint8_t v_includeDelayed_1625_ = stack[1].m_num;
lean_object* v_a_1626_ = stack[2].m_obj;
lean_object* v_a_1627_ = stack[3].m_obj;
lean_object* v_a_1628_ = stack[4].m_obj;
lean_object* v_a_1629_ = stack[5].m_obj;
lean_object* v_res_1651_;
v_res_1651_ = l_Lean_MVarId_getMVarDependencies(v_mvarId_1624_, v_includeDelayed_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object* v_mvarId_1652_, lean_object* v_includeDelayed_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
uint8_t v_includeDelayed_boxed_1659_; lean_object* v_res_1660_; 
v_includeDelayed_boxed_1659_ = lean_unbox(v_includeDelayed_1653_);
v_res_1660_ = l_Lean_MVarId_getMVarDependencies(v_mvarId_1652_, v_includeDelayed_boxed_1659_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
return v_res_1660_;
}
}
lean_object* l_Lean_Expr_getMVarDependencies(lean_object* v_e_1661_, uint8_t v_includeDelayed_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1669_ = lean_st_mk_ref(v___x_1668_);
v___x_1670_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1661_, v_includeDelayed_1662_, v___x_1669_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1678_; 
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v___x_1670_, 0);
lean_dec(v_unused_1679_);
v___x_1672_ = v___x_1670_;
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v___x_1670_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = lean_st_ref_get(v___x_1669_);
lean_dec(v___x_1669_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1674_);
v___x_1676_ = v___x_1672_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v___x_1669_);
v_a_1680_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1670_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1670_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_getMVarDependencies_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1661_ = stack[0].m_obj;
uint8_t v_includeDelayed_1662_ = stack[1].m_num;
lean_object* v_a_1663_ = stack[2].m_obj;
lean_object* v_a_1664_ = stack[3].m_obj;
lean_object* v_a_1665_ = stack[4].m_obj;
lean_object* v_a_1666_ = stack[5].m_obj;
lean_object* v_res_1688_;
v_res_1688_ = l_Lean_Expr_getMVarDependencies(v_e_1661_, v_includeDelayed_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
stack->m_obj
 = v_res_1688_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies___boxed(lean_object* v_e_1689_, lean_object* v_includeDelayed_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
uint8_t v_includeDelayed_boxed_1696_; lean_object* v_res_1697_; 
v_includeDelayed_boxed_1696_ = lean_unbox(v_includeDelayed_1690_);
v_res_1697_ = l_Lean_Expr_getMVarDependencies(v_e_1689_, v_includeDelayed_boxed_1696_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
return v_res_1697_;
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
