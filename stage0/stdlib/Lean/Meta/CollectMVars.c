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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_31_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(lean_object* v_mvarId_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; lean_object* v_mctx_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_50_ = lean_st_ref_get(v___y_48_);
v_mctx_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc_ref(v_mctx_51_);
lean_dec(v___x_50_);
v___x_52_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_51_, v_mvarId_47_);
lean_dec_ref(v_mctx_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg___boxed(lean_object* v_mvarId_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v_mvarId_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec(v_mvarId_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(lean_object* v_mvarId_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v_mvarId_58_, v___y_61_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___boxed(lean_object* v_mvarId_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(v_mvarId_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec(v_mvarId_66_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars(lean_object* v_e_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_74_, v_a_77_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_83_; lean_object* v_result_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_result_87_; lean_object* v_lower_89_; lean_object* v_upper_90_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
v___x_83_ = lean_st_ref_get(v_a_75_);
v_result_84_ = lean_ctor_get(v___x_83_, 1);
lean_inc_ref(v_result_84_);
v___x_85_ = l_Lean_Expr_collectMVars(v___x_83_, v_a_82_);
lean_inc_ref(v___x_85_);
v___x_86_ = lean_st_ref_set(v_a_75_, v___x_85_);
v_result_87_ = lean_ctor_get(v___x_85_, 1);
lean_inc_ref(v_result_87_);
lean_dec_ref(v___x_85_);
v___x_102_ = lean_array_get_size(v_result_84_);
lean_dec_ref(v_result_84_);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_array_get_size(v_result_87_);
v___x_105_ = lean_nat_dec_le(v___x_102_, v___x_103_);
if (v___x_105_ == 0)
{
v_lower_89_ = v___x_102_;
v_upper_90_ = v___x_104_;
goto v___jp_88_;
}
else
{
v_lower_89_ = v___x_103_;
v_upper_90_ = v___x_104_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = l_Array_toSubarray___redArg(v_result_87_, v_lower_89_, v_upper_90_);
v___x_92_ = lean_box(0);
v___x_93_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v___x_91_, v___x_92_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
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
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_81_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_81_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(lean_object* v_a_114_, lean_object* v_b_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_array_122_; lean_object* v_start_123_; lean_object* v_stop_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_153_; 
v_array_122_ = lean_ctor_get(v_a_114_, 0);
v_start_123_ = lean_ctor_get(v_a_114_, 1);
v_stop_124_ = lean_ctor_get(v_a_114_, 2);
v_isSharedCheck_153_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_153_ == 0)
{
v___x_126_ = v_a_114_;
v_isShared_127_ = v_isSharedCheck_153_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_stop_124_);
lean_inc(v_start_123_);
lean_inc(v_array_122_);
lean_dec(v_a_114_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_153_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_lt(v_start_123_, v_stop_124_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_del_object(v___x_126_);
lean_dec(v_stop_124_);
lean_dec(v_start_123_);
lean_dec_ref(v_array_122_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v_b_115_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_array_fget_borrowed(v_array_122_, v_start_123_);
v___x_131_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v___x_130_, v___y_118_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_131_, 1);
v___x_133_ = lean_box(0);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_start_123_, v___x_134_);
lean_dec(v_start_123_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_135_);
v___x_137_ = v___x_126_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_array_122_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_stop_124_);
v___x_137_ = v_reuseFailAlloc_144_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
if (lean_obj_tag(v_a_132_) == 0)
{
v_a_114_ = v___x_137_;
v_b_115_ = v___x_133_;
goto _start;
}
else
{
lean_object* v_val_139_; lean_object* v_mvarIdPending_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_val_139_ = lean_ctor_get(v_a_132_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v_a_132_, 1);
v_mvarIdPending_140_ = lean_ctor_get(v_val_139_, 1);
lean_inc(v_mvarIdPending_140_);
lean_dec(v_val_139_);
v___x_141_ = l_Lean_mkMVar(v_mvarIdPending_140_);
v___x_142_ = l_Lean_Meta_collectMVars(v___x_141_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_dec_ref_known(v___x_142_, 1);
v_a_114_ = v___x_137_;
v_b_115_ = v___x_133_;
goto _start;
}
else
{
lean_dec_ref(v___x_137_);
return v___x_142_;
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_del_object(v___x_126_);
lean_dec(v_stop_124_);
lean_dec(v_start_123_);
lean_dec_ref(v_array_122_);
v_a_145_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_131_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_131_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___boxed(lean_object* v_a_154_, lean_object* v_b_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_154_, v_b_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars___boxed(lean_object* v_e_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Meta_collectMVars(v_e_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(lean_object* v_inst_171_, lean_object* v_R_172_, lean_object* v_a_173_, lean_object* v_b_174_, lean_object* v_c_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_173_, v_b_174_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___boxed(lean_object* v_inst_183_, lean_object* v_R_184_, lean_object* v_a_185_, lean_object* v_b_186_, lean_object* v_c_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(v_inst_183_, v_R_184_, v_a_185_, v_b_186_, v_c_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
return v_res_194_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__0(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_box(0);
v___x_196_ = lean_unsigned_to_nat(16u);
v___x_197_ = lean_mk_array(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__1(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__0, &l_Lean_Meta_getMVars___closed__0_once, _init_l_Lean_Meta_getMVars___closed__0);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__3(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_204_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__1, &l_Lean_Meta_getMVars___closed__1_once, _init_l_Lean_Meta_getMVars___closed__1);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars(lean_object* v_e_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_213_ = lean_st_mk_ref(v___x_212_);
v___x_214_ = l_Lean_Meta_collectMVars(v_e_206_, v___x_213_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_223_; 
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v___x_214_, 0);
lean_dec(v_unused_224_);
v___x_216_ = v___x_214_;
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
else
{
lean_dec(v___x_214_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v_result_219_; lean_object* v___x_221_; 
v___x_218_ = lean_st_ref_get(v___x_213_);
lean_dec(v___x_213_);
v_result_219_ = lean_ctor_get(v___x_218_, 1);
lean_inc_ref(v_result_219_);
lean_dec(v___x_218_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v_result_219_);
v___x_221_ = v___x_216_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_result_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v___x_213_);
v_a_225_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_214_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_214_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars___boxed(lean_object* v_e_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Meta_getMVars(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_239_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_240_, lean_object* v_i_241_, lean_object* v_k_242_){
_start:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_array_get_size(v_keys_240_);
v___x_244_ = lean_nat_dec_lt(v_i_241_, v___x_243_);
if (v___x_244_ == 0)
{
lean_dec(v_i_241_);
return v___x_244_;
}
else
{
lean_object* v_k_x27_245_; uint8_t v___x_246_; 
v_k_x27_245_ = lean_array_fget_borrowed(v_keys_240_, v_i_241_);
v___x_246_ = l_Lean_instBEqMVarId_beq(v_k_242_, v_k_x27_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_add(v_i_241_, v___x_247_);
lean_dec(v_i_241_);
v_i_241_ = v___x_248_;
goto _start;
}
else
{
lean_dec(v_i_241_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_250_, lean_object* v_i_251_, lean_object* v_k_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_250_, v_i_251_, v_k_252_);
lean_dec(v_k_252_);
lean_dec_ref(v_keys_250_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_255_, size_t v_x_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_object* v_es_258_; lean_object* v___x_259_; size_t v___x_260_; size_t v___x_261_; lean_object* v_j_262_; lean_object* v___x_263_; 
v_es_258_ = lean_ctor_get(v_x_255_, 0);
v___x_259_ = lean_box(2);
v___x_260_ = ((size_t)31ULL);
v___x_261_ = lean_usize_land(v_x_256_, v___x_260_);
v_j_262_ = lean_usize_to_nat(v___x_261_);
v___x_263_ = lean_array_get_borrowed(v___x_259_, v_es_258_, v_j_262_);
lean_dec(v_j_262_);
switch(lean_obj_tag(v___x_263_))
{
case 0:
{
lean_object* v_key_264_; uint8_t v___x_265_; 
v_key_264_ = lean_ctor_get(v___x_263_, 0);
v___x_265_ = l_Lean_instBEqMVarId_beq(v_x_257_, v_key_264_);
return v___x_265_;
}
case 1:
{
lean_object* v_node_266_; size_t v___x_267_; size_t v___x_268_; 
v_node_266_ = lean_ctor_get(v___x_263_, 0);
v___x_267_ = ((size_t)5ULL);
v___x_268_ = lean_usize_shift_right(v_x_256_, v___x_267_);
v_x_255_ = v_node_266_;
v_x_256_ = v___x_268_;
goto _start;
}
default: 
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
}
}
else
{
lean_object* v_ks_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_ks_271_ = lean_ctor_get(v_x_255_, 0);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_271_, v___x_272_, v_x_257_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
size_t v_x_1268__boxed_277_; uint8_t v_res_278_; lean_object* v_r_279_; 
v_x_1268__boxed_277_ = lean_unbox_usize(v_x_275_);
lean_dec(v_x_275_);
v_res_278_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_274_, v_x_1268__boxed_277_, v_x_276_);
lean_dec(v_x_276_);
lean_dec_ref(v_x_274_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
uint64_t v___x_282_; size_t v___x_283_; uint8_t v___x_284_; 
v___x_282_ = l_Lean_instHashableMVarId_hash(v_x_281_);
v___x_283_ = lean_uint64_to_usize(v___x_282_);
v___x_284_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_280_, v___x_283_, v_x_281_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg___boxed(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_285_, v_x_286_);
lean_dec(v_x_286_);
lean_dec_ref(v_x_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(lean_object* v_mvarId_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___x_292_; lean_object* v_mctx_293_; lean_object* v_dAssignment_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_292_ = lean_st_ref_get(v___y_290_);
v_mctx_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_mctx_293_);
lean_dec(v___x_292_);
v_dAssignment_294_ = lean_ctor_get(v_mctx_293_, 9);
lean_inc_ref(v_dAssignment_294_);
lean_dec_ref(v_mctx_293_);
v___x_295_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_294_, v_mvarId_289_);
lean_dec_ref(v_dAssignment_294_);
v___x_296_ = lean_box(v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(lean_object* v_mvarId_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec(v_mvarId_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(lean_object* v_as_302_, size_t v_i_303_, size_t v_stop_304_, lean_object* v_b_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_a_312_; uint8_t v___x_316_; 
v___x_316_ = lean_usize_dec_eq(v_i_303_, v_stop_304_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; uint8_t v_a_319_; lean_object* v___x_321_; 
v___x_317_ = lean_array_uget_borrowed(v_as_302_, v_i_303_);
v___x_321_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v___x_317_, v___y_307_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; uint8_t v___x_323_; uint8_t v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_unbox(v_a_322_);
lean_dec(v_a_322_);
v___x_324_ = lean_bool_not(v___x_323_);
v_a_319_ = v___x_324_;
goto v___jp_318_;
}
else
{
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_325_; uint8_t v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_321_, 1);
v___x_326_ = lean_unbox(v_a_325_);
lean_dec(v_a_325_);
v_a_319_ = v___x_326_;
goto v___jp_318_;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_b_305_);
v_a_327_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_321_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_321_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
v___jp_318_:
{
if (v_a_319_ == 0)
{
v_a_312_ = v_b_305_;
goto v___jp_311_;
}
else
{
lean_object* v___x_320_; 
lean_inc(v___x_317_);
v___x_320_ = lean_array_push(v_b_305_, v___x_317_);
v_a_312_ = v___x_320_;
goto v___jp_311_;
}
}
}
else
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v_b_305_);
return v___x_335_;
}
v___jp_311_:
{
size_t v___x_313_; size_t v___x_314_; 
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_add(v_i_303_, v___x_313_);
v_i_303_ = v___x_314_;
v_b_305_ = v_a_312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1___boxed(lean_object* v_as_336_, lean_object* v_i_337_, lean_object* v_stop_338_, lean_object* v_b_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
size_t v_i_boxed_345_; size_t v_stop_boxed_346_; lean_object* v_res_347_; 
v_i_boxed_345_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_stop_boxed_346_ = lean_unbox_usize(v_stop_338_);
lean_dec(v_stop_338_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_336_, v_i_boxed_345_, v_stop_boxed_346_, v_b_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec_ref(v_as_336_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object* v_e_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Meta_getMVars(v_e_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_376_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_376_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_376_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_376_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_array_get_size(v_a_355_);
v___x_361_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_362_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v___x_364_; 
lean_dec(v_a_355_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_361_);
v___x_364_ = v___x_357_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_361_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
uint8_t v___x_366_; 
v___x_366_ = lean_nat_dec_le(v___x_360_, v___x_360_);
if (v___x_366_ == 0)
{
if (v___x_362_ == 0)
{
lean_object* v___x_368_; 
lean_dec(v_a_355_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_361_);
v___x_368_ = v___x_357_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_361_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
lean_del_object(v___x_357_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_360_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_355_, v___x_370_, v___x_371_, v___x_361_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_355_);
return v___x_372_;
}
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
lean_del_object(v___x_357_);
v___x_373_ = ((size_t)0ULL);
v___x_374_ = lean_usize_of_nat(v___x_360_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_355_, v___x_373_, v___x_374_, v___x_361_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_355_);
return v___x_375_;
}
}
}
}
else
{
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object* v_e_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_getMVarsNoDelayed(v_e_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(lean_object* v_mvarId_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_384_, v___y_386_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(lean_object* v_mvarId_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(v_mvarId_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_mvarId_391_);
return v_res_397_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(lean_object* v_00_u03b2_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_399_, v_x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(v_00_u03b2_402_, v_x_403_, v_x_404_);
lean_dec(v_x_404_);
lean_dec_ref(v_x_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_407_, lean_object* v_x_408_, size_t v_x_409_, lean_object* v_x_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_408_, v_x_409_, v_x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
size_t v_x_1477__boxed_416_; uint8_t v_res_417_; lean_object* v_r_418_; 
v_x_1477__boxed_416_ = lean_unbox_usize(v_x_414_);
lean_dec(v_x_414_);
v_res_417_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(v_00_u03b2_412_, v_x_413_, v_x_1477__boxed_416_, v_x_415_);
lean_dec(v_x_415_);
lean_dec_ref(v_x_413_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_419_, lean_object* v_keys_420_, lean_object* v_vals_421_, lean_object* v_heq_422_, lean_object* v_i_423_, lean_object* v_k_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_420_, v_i_423_, v_k_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_426_, lean_object* v_keys_427_, lean_object* v_vals_428_, lean_object* v_heq_429_, lean_object* v_i_430_, lean_object* v_k_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_426_, v_keys_427_, v_vals_428_, v_heq_429_, v_i_430_, v_k_431_);
lean_dec(v_k_431_);
lean_dec_ref(v_vals_428_);
lean_dec_ref(v_keys_427_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_x_434_);
return v___x_442_;
}
else
{
lean_object* v_head_443_; lean_object* v_tail_444_; lean_object* v_type_445_; lean_object* v___x_446_; 
v_head_443_ = lean_ctor_get(v_x_435_, 0);
lean_inc(v_head_443_);
v_tail_444_ = lean_ctor_get(v_x_435_, 1);
lean_inc(v_tail_444_);
lean_dec_ref_known(v_x_435_, 2);
v_type_445_ = lean_ctor_get(v_head_443_, 1);
lean_inc_ref(v_type_445_);
lean_dec(v_head_443_);
v___x_446_ = l_Lean_Meta_collectMVars(v_type_445_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
v_x_434_ = v_a_447_;
v_x_435_ = v_tail_444_;
goto _start;
}
else
{
lean_dec(v_tail_444_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_449_, v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v_x_458_);
return v___x_466_;
}
else
{
lean_object* v_head_467_; lean_object* v_tail_468_; lean_object* v___y_470_; lean_object* v_type_473_; lean_object* v_ctors_474_; lean_object* v___x_475_; 
v_head_467_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_head_467_);
v_tail_468_ = lean_ctor_get(v_x_459_, 1);
lean_inc(v_tail_468_);
lean_dec_ref_known(v_x_459_, 2);
v_type_473_ = lean_ctor_get(v_head_467_, 1);
lean_inc_ref(v_type_473_);
v_ctors_474_ = lean_ctor_get(v_head_467_, 2);
lean_inc(v_ctors_474_);
lean_dec(v_head_467_);
v___x_475_ = l_Lean_Meta_collectMVars(v_type_473_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_a_476_, v_ctors_474_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
v___y_470_ = v___x_477_;
goto v___jp_469_;
}
else
{
lean_dec(v_ctors_474_);
v___y_470_ = v___x_475_;
goto v___jp_469_;
}
v___jp_469_:
{
if (lean_obj_tag(v___y_470_) == 0)
{
lean_object* v_a_471_; 
v_a_471_ = lean_ctor_get(v___y_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___y_470_, 1);
v_x_458_ = v_a_471_;
v_x_459_ = v_tail_468_;
goto _start;
}
else
{
lean_dec(v_tail_468_);
return v___y_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_478_, v_x_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_x_487_);
return v___x_495_;
}
else
{
lean_object* v_head_496_; lean_object* v_tail_497_; lean_object* v___y_499_; lean_object* v_toConstantVal_502_; lean_object* v_value_503_; lean_object* v_type_504_; lean_object* v___x_505_; 
v_head_496_ = lean_ctor_get(v_x_488_, 0);
lean_inc(v_head_496_);
v_tail_497_ = lean_ctor_get(v_x_488_, 1);
lean_inc(v_tail_497_);
lean_dec_ref_known(v_x_488_, 2);
v_toConstantVal_502_ = lean_ctor_get(v_head_496_, 0);
lean_inc_ref(v_toConstantVal_502_);
v_value_503_ = lean_ctor_get(v_head_496_, 1);
lean_inc_ref(v_value_503_);
lean_dec(v_head_496_);
v_type_504_ = lean_ctor_get(v_toConstantVal_502_, 2);
lean_inc_ref(v_type_504_);
lean_dec_ref(v_toConstantVal_502_);
v___x_505_ = l_Lean_Meta_collectMVars(v_type_504_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_506_; 
lean_dec_ref_known(v___x_505_, 1);
v___x_506_ = l_Lean_Meta_collectMVars(v_value_503_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
v___y_499_ = v___x_506_;
goto v___jp_498_;
}
else
{
lean_dec_ref(v_value_503_);
v___y_499_ = v___x_505_;
goto v___jp_498_;
}
v___jp_498_:
{
if (lean_obj_tag(v___y_499_) == 0)
{
lean_object* v_a_500_; 
v_a_500_ = lean_ctor_get(v___y_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___y_499_, 1);
v_x_487_ = v_a_500_;
v_x_488_ = v_tail_497_;
goto _start;
}
else
{
lean_dec(v_tail_497_);
return v___y_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_507_, v_x_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(lean_object* v_d_516_, lean_object* v_a_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
switch(lean_obj_tag(v_d_516_))
{
case 0:
{
lean_object* v_val_524_; lean_object* v_toConstantVal_525_; lean_object* v_type_526_; lean_object* v___x_527_; 
v_val_524_ = lean_ctor_get(v_d_516_, 0);
lean_inc_ref(v_val_524_);
lean_dec_ref_known(v_d_516_, 1);
v_toConstantVal_525_ = lean_ctor_get(v_val_524_, 0);
lean_inc_ref(v_toConstantVal_525_);
lean_dec_ref(v_val_524_);
v_type_526_ = lean_ctor_get(v_toConstantVal_525_, 2);
lean_inc_ref(v_type_526_);
lean_dec_ref(v_toConstantVal_525_);
v___x_527_ = l_Lean_Meta_collectMVars(v_type_526_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_527_;
}
case 4:
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v_a_517_);
return v___x_528_;
}
case 5:
{
lean_object* v_defns_529_; lean_object* v___x_530_; 
v_defns_529_ = lean_ctor_get(v_d_516_, 0);
lean_inc(v_defns_529_);
lean_dec_ref_known(v_d_516_, 1);
v___x_530_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_a_517_, v_defns_529_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_530_;
}
case 6:
{
lean_object* v_types_531_; lean_object* v___x_532_; 
v_types_531_ = lean_ctor_get(v_d_516_, 2);
lean_inc(v_types_531_);
lean_dec_ref_known(v_d_516_, 3);
v___x_532_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_a_517_, v_types_531_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_532_;
}
default: 
{
lean_object* v_val_533_; lean_object* v_toConstantVal_534_; lean_object* v_value_535_; lean_object* v_type_536_; lean_object* v___x_537_; 
v_val_533_ = lean_ctor_get(v_d_516_, 0);
lean_inc_ref(v_val_533_);
lean_dec(v_d_516_);
v_toConstantVal_534_ = lean_ctor_get(v_val_533_, 0);
lean_inc_ref(v_toConstantVal_534_);
v_value_535_ = lean_ctor_get(v_val_533_, 1);
lean_inc_ref(v_value_535_);
lean_dec_ref(v_val_533_);
v_type_536_ = lean_ctor_get(v_toConstantVal_534_, 2);
lean_inc_ref(v_type_536_);
lean_dec_ref(v_toConstantVal_534_);
v___x_537_ = l_Lean_Meta_collectMVars(v_type_536_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; 
lean_dec_ref_known(v___x_537_, 1);
v___x_538_ = l_Lean_Meta_collectMVars(v_value_535_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_538_;
}
else
{
lean_dec_ref(v_value_535_);
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(lean_object* v_d_539_, lean_object* v_a_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_539_, v_a_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object* v_d_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
v___x_556_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_548_, v___x_555_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object* v_d_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_collectMVarsAtDecl(v_d_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object* v_d_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_572_ = lean_st_mk_ref(v___x_571_);
v___x_573_ = l_Lean_Meta_collectMVarsAtDecl(v_d_565_, v___x_572_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_573_, 0);
lean_dec(v_unused_583_);
v___x_575_ = v___x_573_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_dec(v___x_573_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v_result_578_; lean_object* v___x_580_; 
v___x_577_ = lean_st_ref_get(v___x_572_);
lean_dec(v___x_572_);
v_result_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc_ref(v_result_578_);
lean_dec(v___x_577_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_result_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_result_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v___x_572_);
v_a_584_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_573_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_573_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object* v_d_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Meta_getMVarsAtDecl(v_d_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(lean_object* v_mvarId_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; lean_object* v_mctx_603_; lean_object* v_dAssignment_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_602_ = lean_st_ref_get(v___y_600_);
v_mctx_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_mctx_603_);
lean_dec(v___x_602_);
v_dAssignment_604_ = lean_ctor_get(v_mctx_603_, 9);
lean_inc_ref(v_dAssignment_604_);
lean_dec_ref(v_mctx_603_);
v___x_605_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_604_, v_mvarId_599_);
lean_dec_ref(v_dAssignment_604_);
v___x_606_ = lean_box(v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(lean_object* v_mvarId_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec(v_mvarId_608_);
return v_res_611_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(lean_object* v_a_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
uint8_t v___x_614_; 
v___x_614_ = 0;
return v___x_614_;
}
else
{
lean_object* v_key_615_; lean_object* v_tail_616_; uint8_t v___x_617_; 
v_key_615_ = lean_ctor_get(v_x_613_, 0);
v_tail_616_ = lean_ctor_get(v_x_613_, 2);
v___x_617_ = l_Lean_instBEqMVarId_beq(v_key_615_, v_a_612_);
if (v___x_617_ == 0)
{
v_x_613_ = v_tail_616_;
goto _start;
}
else
{
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_619_, lean_object* v_x_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_619_, v_x_620_);
lean_dec(v_x_620_);
lean_dec(v_a_619_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
return v_x_623_;
}
else
{
lean_object* v_key_625_; lean_object* v_value_626_; lean_object* v_tail_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_650_; 
v_key_625_ = lean_ctor_get(v_x_624_, 0);
v_value_626_ = lean_ctor_get(v_x_624_, 1);
v_tail_627_ = lean_ctor_get(v_x_624_, 2);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_650_ == 0)
{
v___x_629_ = v_x_624_;
v_isShared_630_ = v_isSharedCheck_650_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_tail_627_);
lean_inc(v_value_626_);
lean_inc(v_key_625_);
lean_dec(v_x_624_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_650_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v___x_634_; uint64_t v_fold_635_; uint64_t v___x_636_; uint64_t v___x_637_; uint64_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_631_ = lean_array_get_size(v_x_623_);
v___x_632_ = l_Lean_instHashableMVarId_hash(v_key_625_);
v___x_633_ = 32ULL;
v___x_634_ = lean_uint64_shift_right(v___x_632_, v___x_633_);
v_fold_635_ = lean_uint64_xor(v___x_632_, v___x_634_);
v___x_636_ = 16ULL;
v___x_637_ = lean_uint64_shift_right(v_fold_635_, v___x_636_);
v___x_638_ = lean_uint64_xor(v_fold_635_, v___x_637_);
v___x_639_ = lean_uint64_to_usize(v___x_638_);
v___x_640_ = lean_usize_of_nat(v___x_631_);
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_sub(v___x_640_, v___x_641_);
v___x_643_ = lean_usize_land(v___x_639_, v___x_642_);
v___x_644_ = lean_array_uget_borrowed(v_x_623_, v___x_643_);
lean_inc(v___x_644_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 2, v___x_644_);
v___x_646_ = v___x_629_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_key_625_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_value_626_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v___x_644_);
v___x_646_ = v_reuseFailAlloc_649_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; 
v___x_647_ = lean_array_uset(v_x_623_, v___x_643_, v___x_646_);
v_x_623_ = v___x_647_;
v_x_624_ = v_tail_627_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(lean_object* v_i_651_, lean_object* v_source_652_, lean_object* v_target_653_){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = lean_array_get_size(v_source_652_);
v___x_655_ = lean_nat_dec_lt(v_i_651_, v___x_654_);
if (v___x_655_ == 0)
{
lean_dec_ref(v_source_652_);
lean_dec(v_i_651_);
return v_target_653_;
}
else
{
lean_object* v_es_656_; lean_object* v___x_657_; lean_object* v_source_658_; lean_object* v_target_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_es_656_ = lean_array_fget(v_source_652_, v_i_651_);
v___x_657_ = lean_box(0);
v_source_658_ = lean_array_fset(v_source_652_, v_i_651_, v___x_657_);
v_target_659_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_target_653_, v_es_656_);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_add(v_i_651_, v___x_660_);
lean_dec(v_i_651_);
v_i_651_ = v___x_661_;
v_source_652_ = v_source_658_;
v_target_653_ = v_target_659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(lean_object* v_data_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_nbuckets_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_664_ = lean_array_get_size(v_data_663_);
v___x_665_ = lean_unsigned_to_nat(2u);
v_nbuckets_666_ = lean_nat_mul(v___x_664_, v___x_665_);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_box(0);
v___x_669_ = lean_mk_array(v_nbuckets_666_, v___x_668_);
v___x_670_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v___x_667_, v_data_663_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(lean_object* v_m_671_, lean_object* v_a_672_, lean_object* v_b_673_){
_start:
{
lean_object* v_size_674_; lean_object* v_buckets_675_; lean_object* v___x_676_; uint64_t v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v_fold_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v_bkt_689_; uint8_t v___x_690_; 
v_size_674_ = lean_ctor_get(v_m_671_, 0);
v_buckets_675_ = lean_ctor_get(v_m_671_, 1);
v___x_676_ = lean_array_get_size(v_buckets_675_);
v___x_677_ = l_Lean_instHashableMVarId_hash(v_a_672_);
v___x_678_ = 32ULL;
v___x_679_ = lean_uint64_shift_right(v___x_677_, v___x_678_);
v_fold_680_ = lean_uint64_xor(v___x_677_, v___x_679_);
v___x_681_ = 16ULL;
v___x_682_ = lean_uint64_shift_right(v_fold_680_, v___x_681_);
v___x_683_ = lean_uint64_xor(v_fold_680_, v___x_682_);
v___x_684_ = lean_uint64_to_usize(v___x_683_);
v___x_685_ = lean_usize_of_nat(v___x_676_);
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_sub(v___x_685_, v___x_686_);
v___x_688_ = lean_usize_land(v___x_684_, v___x_687_);
v_bkt_689_ = lean_array_uget_borrowed(v_buckets_675_, v___x_688_);
v___x_690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_672_, v_bkt_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_711_; 
lean_inc_ref(v_buckets_675_);
lean_inc(v_size_674_);
v_isSharedCheck_711_ = !lean_is_exclusive(v_m_671_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_712_ = lean_ctor_get(v_m_671_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_m_671_, 0);
lean_dec(v_unused_713_);
v___x_692_ = v_m_671_;
v_isShared_693_ = v_isSharedCheck_711_;
goto v_resetjp_691_;
}
else
{
lean_dec(v_m_671_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_711_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v_size_x27_695_; lean_object* v___x_696_; lean_object* v_buckets_x27_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v_size_x27_695_ = lean_nat_add(v_size_674_, v___x_694_);
lean_dec(v_size_674_);
lean_inc(v_bkt_689_);
v___x_696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_696_, 0, v_a_672_);
lean_ctor_set(v___x_696_, 1, v_b_673_);
lean_ctor_set(v___x_696_, 2, v_bkt_689_);
v_buckets_x27_697_ = lean_array_uset(v_buckets_675_, v___x_688_, v___x_696_);
v___x_698_ = lean_unsigned_to_nat(4u);
v___x_699_ = lean_nat_mul(v_size_x27_695_, v___x_698_);
v___x_700_ = lean_unsigned_to_nat(3u);
v___x_701_ = lean_nat_div(v___x_699_, v___x_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_array_get_size(v_buckets_x27_697_);
v___x_703_ = lean_nat_dec_le(v___x_701_, v___x_702_);
lean_dec(v___x_701_);
if (v___x_703_ == 0)
{
lean_object* v_val_704_; lean_object* v___x_706_; 
v_val_704_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_buckets_x27_697_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v_val_704_);
lean_ctor_set(v___x_692_, 0, v_size_x27_695_);
v___x_706_ = v___x_692_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_size_x27_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_val_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
else
{
lean_object* v___x_709_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v_buckets_x27_697_);
lean_ctor_set(v___x_692_, 0, v_size_x27_695_);
v___x_709_ = v___x_692_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_size_x27_695_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_buckets_x27_697_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_dec(v_b_673_);
lean_dec(v_a_672_);
return v_m_671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(uint8_t v_includeDelayed_714_, lean_object* v_as_715_, size_t v_sz_716_, size_t v_i_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_a_726_; uint8_t v___x_730_; 
v___x_730_ = lean_usize_dec_lt(v_i_717_, v_sz_716_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v_b_718_);
return v___x_731_;
}
else
{
lean_object* v_a_732_; uint8_t v_a_737_; 
v_a_732_ = lean_array_uget_borrowed(v_as_715_, v_i_717_);
if (v_includeDelayed_714_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_a_732_, v___y_721_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; uint8_t v___x_740_; uint8_t v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = lean_unbox(v_a_739_);
lean_dec(v_a_739_);
v___x_741_ = lean_bool_not(v___x_740_);
v_a_737_ = v___x_741_;
goto v___jp_736_;
}
else
{
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_742_; uint8_t v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_738_, 1);
v___x_743_ = lean_unbox(v_a_742_);
lean_dec(v_a_742_);
v_a_737_ = v___x_743_;
goto v___jp_736_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_b_718_);
v_a_744_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_738_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_738_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
else
{
goto v___jp_733_;
}
v___jp_733_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
lean_inc(v_a_732_);
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_b_718_, v_a_732_, v___x_734_);
v_a_726_ = v___x_735_;
goto v___jp_725_;
}
v___jp_736_:
{
if (v_a_737_ == 0)
{
v_a_726_ = v_b_718_;
goto v___jp_725_;
}
else
{
goto v___jp_733_;
}
}
}
v___jp_725_:
{
size_t v___x_727_; size_t v___x_728_; 
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_717_, v___x_727_);
v_i_717_ = v___x_728_;
v_b_718_ = v_a_726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___boxed(lean_object* v_includeDelayed_752_, lean_object* v_as_753_, lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_b_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
uint8_t v_includeDelayed_boxed_763_; size_t v_sz_boxed_764_; size_t v_i_boxed_765_; lean_object* v_res_766_; 
v_includeDelayed_boxed_763_ = lean_unbox(v_includeDelayed_752_);
v_sz_boxed_764_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_765_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_boxed_763_, v_as_753_, v_sz_boxed_764_, v_i_boxed_765_, v_b_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v_as_753_);
return v_res_766_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = l_Lean_maxRecDepthErrorMessage;
v___x_773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3);
v___x_775_ = l_Lean_MessageData_ofFormat(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4);
v___x_777_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2));
v___x_778_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(lean_object* v_ref_779_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_ref_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(lean_object* v_ref_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(lean_object* v_mvarId_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_mctx_791_; lean_object* v_eAssignment_792_; lean_object* v_dAssignment_793_; uint8_t v___x_794_; 
v___x_790_ = lean_st_ref_get(v___y_788_);
v_mctx_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc_ref(v_mctx_791_);
lean_dec(v___x_790_);
v_eAssignment_792_ = lean_ctor_get(v_mctx_791_, 8);
lean_inc_ref(v_eAssignment_792_);
v_dAssignment_793_ = lean_ctor_get(v_mctx_791_, 9);
lean_inc_ref(v_dAssignment_793_);
lean_dec_ref(v_mctx_791_);
v___x_794_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_eAssignment_792_, v_mvarId_787_);
lean_dec_ref(v_eAssignment_792_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_793_, v_mvarId_787_);
lean_dec_ref(v_dAssignment_793_);
v___x_796_ = lean_box(v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_dAssignment_793_);
v___x_798_ = lean_box(v___x_794_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(lean_object* v_mvarId_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec(v_mvarId_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(lean_object* v_mvarId_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; lean_object* v_mctx_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_807_ = lean_st_ref_get(v___y_805_);
v_mctx_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc_ref(v_mctx_808_);
lean_dec(v___x_807_);
v___x_809_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_808_, v_mvarId_804_);
lean_dec_ref(v_mctx_808_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg___boxed(lean_object* v_mvarId_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec(v_mvarId_811_);
return v_res_814_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_box(0);
v___x_816_ = lean_unsigned_to_nat(16u);
v___x_817_ = lean_mk_array(v___x_816_, v___x_815_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0);
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___x_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars(lean_object* v_e_821_, uint8_t v_includeDelayed_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_getMVars(v_e_821_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = lean_st_ref_get(v_a_823_);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_834_ = lean_st_ref_set(v_a_823_, v___x_833_);
v_sz_835_ = lean_array_size(v_a_830_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_822_, v_a_830_, v_sz_835_, v___x_836_, v___x_831_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_857_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_857_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_857_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_857_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_842_ = lean_st_ref_set(v_a_823_, v_a_838_);
v___x_843_ = lean_array_get_size(v_a_830_);
v___x_844_ = lean_box(0);
v___x_845_ = lean_nat_dec_lt(v___x_832_, v___x_843_);
if (v___x_845_ == 0)
{
lean_object* v___x_847_; 
lean_dec(v_a_830_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_844_);
v___x_847_ = v___x_840_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_844_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
else
{
uint8_t v___x_849_; 
v___x_849_ = lean_nat_dec_le(v___x_843_, v___x_843_);
if (v___x_849_ == 0)
{
if (v___x_845_ == 0)
{
lean_object* v___x_851_; 
lean_dec(v_a_830_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_844_);
v___x_851_ = v___x_840_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_844_);
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
size_t v___x_853_; lean_object* v___x_854_; 
lean_del_object(v___x_840_);
v___x_853_ = lean_usize_of_nat(v___x_843_);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_830_, v___x_836_, v___x_853_, v___x_844_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec(v_a_830_);
return v___x_854_;
}
}
else
{
size_t v___x_855_; lean_object* v___x_856_; 
lean_del_object(v___x_840_);
v___x_855_ = lean_usize_of_nat(v___x_843_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_830_, v___x_836_, v___x_855_, v___x_844_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec(v_a_830_);
return v___x_856_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_830_);
v_a_858_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_837_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_837_);
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
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_829_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_829_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(lean_object* v_init_874_, uint8_t v_includeDelayed_875_, uint8_t v___y_876_, lean_object* v_as_877_, size_t v_sz_878_, size_t v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v___x_887_; 
v___x_887_ = lean_usize_dec_lt(v_i_879_, v_sz_878_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_b_880_);
return v___x_888_;
}
else
{
lean_object* v_snd_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_923_; 
v_snd_889_ = lean_ctor_get(v_b_880_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v_b_880_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_b_880_, 0);
lean_dec(v_unused_924_);
v___x_891_ = v_b_880_;
v_isShared_892_ = v_isSharedCheck_923_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_snd_889_);
lean_dec(v_b_880_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_923_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_a_893_; lean_object* v___x_894_; 
v_a_893_ = lean_array_uget_borrowed(v_as_877_, v_i_879_);
lean_inc(v_snd_889_);
v___x_894_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_874_, v_includeDelayed_875_, v___y_876_, v_a_893_, v_snd_889_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_914_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_914_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_914_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_914_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
if (lean_obj_tag(v_a_895_) == 0)
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_a_895_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_899_);
v___x_901_ = v___x_891_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_snd_889_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_901_);
v___x_903_ = v___x_897_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_del_object(v___x_897_);
lean_dec(v_snd_889_);
v_a_906_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v_a_895_, 1);
v___x_907_ = lean_box(0);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 1, v_a_906_);
lean_ctor_set(v___x_891_, 0, v___x_907_);
v___x_909_ = v___x_891_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_a_906_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
size_t v___x_910_; size_t v___x_911_; 
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_add(v_i_879_, v___x_910_);
v_i_879_ = v___x_911_;
v_b_880_ = v___x_909_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_del_object(v___x_891_);
lean_dec(v_snd_889_);
v_a_915_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_894_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_894_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(uint8_t v_includeDelayed_925_, uint8_t v___y_926_, lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v_b_930_);
return v___x_938_;
}
else
{
lean_object* v_snd_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_976_; 
v_snd_939_ = lean_ctor_get(v_b_930_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_b_930_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_b_930_, 0);
lean_dec(v_unused_977_);
v___x_941_ = v_b_930_;
v_isShared_942_ = v_isSharedCheck_976_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snd_939_);
lean_dec(v_b_930_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_976_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v_a_945_; lean_object* v_a_952_; 
v___x_943_ = lean_box(0);
v_a_952_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
if (lean_obj_tag(v_a_952_) == 0)
{
v_a_945_ = v_snd_939_;
goto v___jp_944_;
}
else
{
lean_object* v_val_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_snd_939_);
v_val_953_ = lean_ctor_get(v_a_952_, 0);
v___x_954_ = l_Lean_LocalDecl_type(v_val_953_);
v___x_955_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_954_, v_includeDelayed_925_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec_ref_known(v___x_955_, 1);
v___x_956_ = lean_box(0);
v___x_957_ = l_Lean_LocalDecl_value_x3f(v_val_953_, v___y_926_);
if (lean_obj_tag(v___x_957_) == 1)
{
lean_object* v_val_958_; lean_object* v___x_959_; 
v_val_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_958_, v_includeDelayed_925_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_dec_ref_known(v___x_959_, 1);
v_a_945_ = v___x_956_;
goto v___jp_944_;
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_del_object(v___x_941_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_dec(v___x_957_);
v_a_945_ = v___x_956_;
goto v___jp_944_;
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_del_object(v___x_941_);
v_a_968_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_955_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_955_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
v___jp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_a_945_);
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_947_ = v___x_941_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_a_945_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
size_t v___x_948_; size_t v___x_949_; 
v___x_948_ = ((size_t)1ULL);
v___x_949_ = lean_usize_add(v_i_929_, v___x_948_);
v_i_929_ = v___x_949_;
v_b_930_ = v___x_947_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(uint8_t v_includeDelayed_978_, uint8_t v___y_979_, lean_object* v_as_980_, size_t v_sz_981_, size_t v_i_982_, lean_object* v_b_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = lean_usize_dec_lt(v_i_982_, v_sz_981_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_b_983_);
return v___x_991_;
}
else
{
lean_object* v_snd_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1029_; 
v_snd_992_ = lean_ctor_get(v_b_983_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_b_983_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_b_983_, 0);
lean_dec(v_unused_1030_);
v___x_994_ = v_b_983_;
v_isShared_995_ = v_isSharedCheck_1029_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_992_);
lean_dec(v_b_983_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1029_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v_a_998_; lean_object* v_a_1005_; 
v___x_996_ = lean_box(0);
v_a_1005_ = lean_array_uget_borrowed(v_as_980_, v_i_982_);
if (lean_obj_tag(v_a_1005_) == 0)
{
v_a_998_ = v_snd_992_;
goto v___jp_997_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec(v_snd_992_);
v_val_1006_ = lean_ctor_get(v_a_1005_, 0);
v___x_1007_ = l_Lean_LocalDecl_type(v_val_1006_);
v___x_1008_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1007_, v_includeDelayed_978_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec_ref_known(v___x_1008_, 1);
v___x_1009_ = lean_box(0);
v___x_1010_ = l_Lean_LocalDecl_value_x3f(v_val_1006_, v___y_979_);
if (lean_obj_tag(v___x_1010_) == 1)
{
lean_object* v_val_1011_; lean_object* v___x_1012_; 
v_val_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1011_, v_includeDelayed_978_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_dec_ref_known(v___x_1012_, 1);
v_a_998_ = v___x_1009_;
goto v___jp_997_;
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_994_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
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
else
{
lean_dec(v___x_1010_);
v_a_998_ = v___x_1009_;
goto v___jp_997_;
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_del_object(v___x_994_);
v_a_1021_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1008_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1008_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
v___jp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v_a_998_);
lean_ctor_set(v___x_994_, 0, v___x_996_);
v___x_1000_ = v___x_994_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_a_998_);
v___x_1000_ = v_reuseFailAlloc_1004_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_add(v_i_982_, v___x_1001_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_978_, v___y_979_, v_as_980_, v_sz_981_, v___x_1002_, v___x_1000_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_1003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(lean_object* v_init_1031_, uint8_t v_includeDelayed_1032_, uint8_t v___y_1033_, lean_object* v_n_1034_, lean_object* v_b_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
if (lean_obj_tag(v_n_1034_) == 0)
{
lean_object* v_cs_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; size_t v_sz_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v_cs_1042_ = lean_ctor_get(v_n_1034_, 0);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v_b_1035_);
v_sz_1045_ = lean_array_size(v_cs_1042_);
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_1031_, v_includeDelayed_1032_, v___y_1033_, v_cs_1042_, v_sz_1045_, v___x_1046_, v___x_1044_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
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
else
{
lean_object* v_vs_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; size_t v_sz_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
v_vs_1071_ = lean_ctor_get(v_n_1034_, 0);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_b_1035_);
v_sz_1074_ = lean_array_size(v_vs_1071_);
v___x_1075_ = ((size_t)0ULL);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_1032_, v___y_1033_, v_vs_1071_, v_sz_1074_, v___x_1075_, v___x_1073_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1091_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1091_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1091_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_fst_1081_; 
v_fst_1081_ = lean_ctor_get(v_a_1077_, 0);
if (lean_obj_tag(v_fst_1081_) == 0)
{
lean_object* v_snd_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v_snd_1082_ = lean_ctor_get(v_a_1077_, 1);
lean_inc(v_snd_1082_);
lean_dec(v_a_1077_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_snd_1082_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1083_);
v___x_1085_ = v___x_1079_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
else
{
lean_object* v_val_1087_; lean_object* v___x_1089_; 
lean_inc_ref(v_fst_1081_);
lean_dec(v_a_1077_);
v_val_1087_ = lean_ctor_get(v_fst_1081_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v_fst_1081_, 1);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_val_1087_);
v___x_1089_ = v___x_1079_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_val_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1076_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1076_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(uint8_t v_includeDelayed_1100_, uint8_t v___y_1101_, lean_object* v_as_1102_, size_t v_sz_1103_, size_t v_i_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_usize_dec_lt(v_i_1104_, v_sz_1103_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_b_1105_);
return v___x_1113_;
}
else
{
lean_object* v_snd_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1151_; 
v_snd_1114_ = lean_ctor_get(v_b_1105_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_b_1105_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v_b_1105_, 0);
lean_dec(v_unused_1152_);
v___x_1116_ = v_b_1105_;
v_isShared_1117_ = v_isSharedCheck_1151_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_snd_1114_);
lean_dec(v_b_1105_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1151_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v_a_1120_; lean_object* v_a_1127_; 
v___x_1118_ = lean_box(0);
v_a_1127_ = lean_array_uget_borrowed(v_as_1102_, v_i_1104_);
if (lean_obj_tag(v_a_1127_) == 0)
{
v_a_1120_ = v_snd_1114_;
goto v___jp_1119_;
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec(v_snd_1114_);
v_val_1128_ = lean_ctor_get(v_a_1127_, 0);
v___x_1129_ = l_Lean_LocalDecl_type(v_val_1128_);
v___x_1130_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1129_, v_includeDelayed_1100_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1130_, 1);
v___x_1131_ = lean_box(0);
v___x_1132_ = l_Lean_LocalDecl_value_x3f(v_val_1128_, v___y_1101_);
if (lean_obj_tag(v___x_1132_) == 1)
{
lean_object* v_val_1133_; lean_object* v___x_1134_; 
v_val_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_val_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1133_, v_includeDelayed_1100_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_dec_ref_known(v___x_1134_, 1);
v_a_1120_ = v___x_1131_;
goto v___jp_1119_;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_del_object(v___x_1116_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
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
else
{
lean_dec(v___x_1132_);
v_a_1120_ = v___x_1131_;
goto v___jp_1119_;
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_del_object(v___x_1116_);
v_a_1143_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1130_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1130_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
v___jp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 1, v_a_1120_);
lean_ctor_set(v___x_1116_, 0, v___x_1118_);
v___x_1122_ = v___x_1116_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_a_1120_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
size_t v___x_1123_; size_t v___x_1124_; 
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_add(v_i_1104_, v___x_1123_);
v_i_1104_ = v___x_1124_;
v_b_1105_ = v___x_1122_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(uint8_t v_includeDelayed_1153_, uint8_t v___y_1154_, lean_object* v_as_1155_, size_t v_sz_1156_, size_t v_i_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_usize_dec_lt(v_i_1157_, v_sz_1156_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v_b_1158_);
return v___x_1166_;
}
else
{
lean_object* v_snd_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1204_; 
v_snd_1167_ = lean_ctor_get(v_b_1158_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_b_1158_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v_b_1158_, 0);
lean_dec(v_unused_1205_);
v___x_1169_ = v_b_1158_;
v_isShared_1170_ = v_isSharedCheck_1204_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1167_);
lean_dec(v_b_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1204_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v_a_1173_; lean_object* v_a_1180_; 
v___x_1171_ = lean_box(0);
v_a_1180_ = lean_array_uget_borrowed(v_as_1155_, v_i_1157_);
if (lean_obj_tag(v_a_1180_) == 0)
{
v_a_1173_ = v_snd_1167_;
goto v___jp_1172_;
}
else
{
lean_object* v_val_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_snd_1167_);
v_val_1181_ = lean_ctor_get(v_a_1180_, 0);
v___x_1182_ = l_Lean_LocalDecl_type(v_val_1181_);
v___x_1183_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1182_, v_includeDelayed_1153_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref_known(v___x_1183_, 1);
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Lean_LocalDecl_value_x3f(v_val_1181_, v___y_1154_);
if (lean_obj_tag(v___x_1185_) == 1)
{
lean_object* v_val_1186_; lean_object* v___x_1187_; 
v_val_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_val_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1186_, v_includeDelayed_1153_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_dec_ref_known(v___x_1187_, 1);
v_a_1173_ = v___x_1184_;
goto v___jp_1172_;
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_del_object(v___x_1169_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_dec(v___x_1185_);
v_a_1173_ = v___x_1184_;
goto v___jp_1172_;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1169_);
v_a_1196_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1183_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1183_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
v___jp_1172_:
{
lean_object* v___x_1175_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_a_1173_);
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1175_ = v___x_1169_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_a_1173_);
v___x_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
size_t v___x_1176_; size_t v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = ((size_t)1ULL);
v___x_1177_ = lean_usize_add(v_i_1157_, v___x_1176_);
v___x_1178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_1153_, v___y_1154_, v_as_1155_, v_sz_1156_, v___x_1177_, v___x_1175_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(uint8_t v_includeDelayed_1206_, uint8_t v___y_1207_, lean_object* v_t_1208_, lean_object* v_init_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_root_1216_; lean_object* v_tail_1217_; lean_object* v___x_1218_; 
v_root_1216_ = lean_ctor_get(v_t_1208_, 0);
v_tail_1217_ = lean_ctor_get(v_t_1208_, 1);
v___x_1218_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1209_, v_includeDelayed_1206_, v___y_1207_, v_root_1216_, v_init_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1255_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1255_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1255_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
if (lean_obj_tag(v_a_1219_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; 
v_a_1223_ = lean_ctor_get(v_a_1219_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v_a_1219_, 1);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_a_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; size_t v_sz_1230_; size_t v___x_1231_; lean_object* v___x_1232_; 
lean_del_object(v___x_1221_);
v_a_1227_ = lean_ctor_get(v_a_1219_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v_a_1219_, 1);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v_a_1227_);
v_sz_1230_ = lean_array_size(v_tail_1217_);
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_1206_, v___y_1207_, v_tail_1217_, v_sz_1230_, v___x_1231_, v___x_1229_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1246_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1246_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1246_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_fst_1237_; 
v_fst_1237_ = lean_ctor_get(v_a_1233_, 0);
if (lean_obj_tag(v_fst_1237_) == 0)
{
lean_object* v_snd_1238_; lean_object* v___x_1240_; 
v_snd_1238_ = lean_ctor_get(v_a_1233_, 1);
lean_inc(v_snd_1238_);
lean_dec(v_a_1233_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_snd_1238_);
v___x_1240_ = v___x_1235_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_snd_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
else
{
lean_object* v_val_1242_; lean_object* v___x_1244_; 
lean_inc_ref(v_fst_1237_);
lean_dec(v_a_1233_);
v_val_1242_ = lean_ctor_get(v_fst_1237_, 0);
lean_inc(v_val_1242_);
lean_dec_ref_known(v_fst_1237_, 1);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_val_1242_);
v___x_1244_ = v___x_1235_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_val_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1232_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1232_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1218_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1218_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object* v_mvarId_1264_, uint8_t v_includeDelayed_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; uint8_t v_a_1276_; lean_object* v_fileName_1282_; lean_object* v_fileMap_1283_; lean_object* v_options_1284_; lean_object* v_currRecDepth_1285_; lean_object* v_maxRecDepth_1286_; lean_object* v_ref_1287_; lean_object* v_currNamespace_1288_; lean_object* v_openDecls_1289_; lean_object* v_initHeartbeats_1290_; lean_object* v_maxHeartbeats_1291_; lean_object* v_quotContext_1292_; lean_object* v_currMacroScope_1293_; uint8_t v_diag_1294_; lean_object* v_cancelTk_x3f_1295_; uint8_t v_suppressElabErrors_1296_; lean_object* v_inheritedTraceOptions_1297_; uint8_t v___y_1299_; lean_object* v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; 
v_fileName_1282_ = lean_ctor_get(v_a_1269_, 0);
lean_inc_ref(v_fileName_1282_);
v_fileMap_1283_ = lean_ctor_get(v_a_1269_, 1);
lean_inc_ref(v_fileMap_1283_);
v_options_1284_ = lean_ctor_get(v_a_1269_, 2);
lean_inc_ref(v_options_1284_);
v_currRecDepth_1285_ = lean_ctor_get(v_a_1269_, 3);
lean_inc(v_currRecDepth_1285_);
v_maxRecDepth_1286_ = lean_ctor_get(v_a_1269_, 4);
lean_inc(v_maxRecDepth_1286_);
v_ref_1287_ = lean_ctor_get(v_a_1269_, 5);
lean_inc(v_ref_1287_);
v_currNamespace_1288_ = lean_ctor_get(v_a_1269_, 6);
lean_inc(v_currNamespace_1288_);
v_openDecls_1289_ = lean_ctor_get(v_a_1269_, 7);
lean_inc(v_openDecls_1289_);
v_initHeartbeats_1290_ = lean_ctor_get(v_a_1269_, 8);
lean_inc(v_initHeartbeats_1290_);
v_maxHeartbeats_1291_ = lean_ctor_get(v_a_1269_, 9);
lean_inc(v_maxHeartbeats_1291_);
v_quotContext_1292_ = lean_ctor_get(v_a_1269_, 10);
lean_inc(v_quotContext_1292_);
v_currMacroScope_1293_ = lean_ctor_get(v_a_1269_, 11);
lean_inc(v_currMacroScope_1293_);
v_diag_1294_ = lean_ctor_get_uint8(v_a_1269_, sizeof(void*)*14);
v_cancelTk_x3f_1295_ = lean_ctor_get(v_a_1269_, 12);
lean_inc(v_cancelTk_x3f_1295_);
v_suppressElabErrors_1296_ = lean_ctor_get_uint8(v_a_1269_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1297_ = lean_ctor_get(v_a_1269_, 13);
lean_inc_ref(v_inheritedTraceOptions_1297_);
lean_dec_ref(v_a_1269_);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_nat_dec_eq(v_maxRecDepth_1286_, v___x_1353_);
v___x_1355_ = lean_bool_not(v___x_1354_);
if (v___x_1355_ == 0)
{
v___y_1299_ = v___x_1355_;
goto v___jp_1298_;
}
else
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_nat_dec_eq(v_currRecDepth_1285_, v_maxRecDepth_1286_);
v___y_1299_ = v___x_1356_;
goto v___jp_1298_;
}
v___jp_1272_:
{
if (v_a_1276_ == 0)
{
v_mvarId_1264_ = v___y_1273_;
v_a_1269_ = v___y_1274_;
goto _start;
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_st_ref_take(v_a_1266_);
lean_inc(v___y_1273_);
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_1278_, v___y_1273_, v___y_1275_);
v___x_1280_ = lean_st_ref_set(v_a_1266_, v___x_1279_);
v_mvarId_1264_ = v___y_1273_;
v_a_1269_ = v___y_1274_;
goto _start;
}
}
v___jp_1298_:
{
if (v___y_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_add(v_currRecDepth_1285_, v___x_1300_);
lean_dec(v_currRecDepth_1285_);
v___x_1302_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1302_, 0, v_fileName_1282_);
lean_ctor_set(v___x_1302_, 1, v_fileMap_1283_);
lean_ctor_set(v___x_1302_, 2, v_options_1284_);
lean_ctor_set(v___x_1302_, 3, v___x_1301_);
lean_ctor_set(v___x_1302_, 4, v_maxRecDepth_1286_);
lean_ctor_set(v___x_1302_, 5, v_ref_1287_);
lean_ctor_set(v___x_1302_, 6, v_currNamespace_1288_);
lean_ctor_set(v___x_1302_, 7, v_openDecls_1289_);
lean_ctor_set(v___x_1302_, 8, v_initHeartbeats_1290_);
lean_ctor_set(v___x_1302_, 9, v_maxHeartbeats_1291_);
lean_ctor_set(v___x_1302_, 10, v_quotContext_1292_);
lean_ctor_set(v___x_1302_, 11, v_currMacroScope_1293_);
lean_ctor_set(v___x_1302_, 12, v_cancelTk_x3f_1295_);
lean_ctor_set(v___x_1302_, 13, v_inheritedTraceOptions_1297_);
lean_ctor_set_uint8(v___x_1302_, sizeof(void*)*14, v_diag_1294_);
lean_ctor_set_uint8(v___x_1302_, sizeof(void*)*14 + 1, v_suppressElabErrors_1296_);
lean_inc(v_mvarId_1264_);
v___x_1303_ = l_Lean_MVarId_getDecl(v_mvarId_1264_, v_a_1267_, v_a_1268_, v___x_1302_, v_a_1270_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v_lctx_1305_; lean_object* v_type_1306_; lean_object* v___x_1307_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v_lctx_1305_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_lctx_1305_);
v_type_1306_ = lean_ctor_get(v_a_1304_, 2);
lean_inc_ref(v_type_1306_);
lean_dec(v_a_1304_);
v___x_1307_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_type_1306_, v_includeDelayed_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v___x_1302_, v_a_1270_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_decls_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref_known(v___x_1307_, 1);
v_decls_1308_ = lean_ctor_get(v_lctx_1305_, 1);
lean_inc_ref(v_decls_1308_);
lean_dec_ref(v_lctx_1305_);
v___x_1309_ = lean_box(0);
v___x_1310_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_1265_, v___y_1299_, v_decls_1308_, v___x_1309_, v_a_1266_, v_a_1267_, v_a_1268_, v___x_1302_, v_a_1270_);
lean_dec_ref(v_decls_1308_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v___x_1311_; 
lean_dec_ref_known(v___x_1310_, 1);
v___x_1311_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1264_, v_a_1268_);
lean_dec(v_mvarId_1264_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1335_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1335_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1335_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
if (lean_obj_tag(v_a_1312_) == 1)
{
lean_object* v_val_1316_; lean_object* v_mvarIdPending_1317_; lean_object* v___x_1318_; 
lean_del_object(v___x_1314_);
v_val_1316_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v_a_1312_, 1);
v_mvarIdPending_1317_ = lean_ctor_get(v_val_1316_, 1);
lean_inc(v_mvarIdPending_1317_);
lean_dec(v_val_1316_);
v___x_1318_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarIdPending_1317_, v_a_1268_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; uint8_t v___x_1320_; uint8_t v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = lean_unbox(v_a_1319_);
lean_dec(v_a_1319_);
v___x_1321_ = lean_bool_not(v___x_1320_);
v___y_1273_ = v_mvarIdPending_1317_;
v___y_1274_ = v___x_1302_;
v___y_1275_ = v___x_1309_;
v_a_1276_ = v___x_1321_;
goto v___jp_1272_;
}
else
{
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1322_; uint8_t v___x_1323_; 
v_a_1322_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1323_ = lean_unbox(v_a_1322_);
lean_dec(v_a_1322_);
v___y_1273_ = v_mvarIdPending_1317_;
v___y_1274_ = v___x_1302_;
v___y_1275_ = v___x_1309_;
v_a_1276_ = v___x_1323_;
goto v___jp_1272_;
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_mvarIdPending_1317_);
lean_dec_ref_known(v___x_1302_, 14);
v_a_1324_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1318_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1318_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
else
{
lean_object* v___x_1333_; 
lean_dec(v_a_1312_);
lean_dec_ref_known(v___x_1302_, 14);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1309_);
v___x_1333_ = v___x_1314_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1309_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref_known(v___x_1302_, 14);
v_a_1336_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1311_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1311_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1302_, 14);
lean_dec(v_mvarId_1264_);
return v___x_1310_;
}
}
else
{
lean_dec_ref(v_lctx_1305_);
lean_dec_ref_known(v___x_1302_, 14);
lean_dec(v_mvarId_1264_);
return v___x_1307_;
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref_known(v___x_1302_, 14);
lean_dec(v_mvarId_1264_);
v_a_1344_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1303_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1303_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v___x_1352_; 
lean_dec_ref(v_inheritedTraceOptions_1297_);
lean_dec(v_cancelTk_x3f_1295_);
lean_dec(v_currMacroScope_1293_);
lean_dec(v_quotContext_1292_);
lean_dec(v_maxHeartbeats_1291_);
lean_dec(v_initHeartbeats_1290_);
lean_dec(v_openDecls_1289_);
lean_dec(v_currNamespace_1288_);
lean_dec(v_maxRecDepth_1286_);
lean_dec(v_currRecDepth_1285_);
lean_dec_ref(v_options_1284_);
lean_dec_ref(v_fileMap_1283_);
lean_dec_ref(v_fileName_1282_);
lean_dec(v_mvarId_1264_);
v___x_1352_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1287_);
return v___x_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(lean_object* v_as_1357_, size_t v_i_1358_, size_t v_stop_1359_, lean_object* v_b_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v___x_1367_; 
v___x_1367_ = lean_usize_dec_eq(v_i_1358_, v_stop_1359_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_array_uget_borrowed(v_as_1357_, v_i_1358_);
lean_inc_ref(v___y_1364_);
lean_inc(v___x_1368_);
v___x_1369_ = l___private_Lean_Meta_CollectMVars_0__go(v___x_1368_, v___x_1367_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; size_t v___x_1371_; size_t v___x_1372_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = lean_usize_add(v_i_1358_, v___x_1371_);
v_i_1358_ = v___x_1372_;
v_b_1360_ = v_a_1370_;
goto _start;
}
else
{
return v___x_1369_;
}
}
else
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_b_1360_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object* v_as_1375_, lean_object* v_i_1376_, lean_object* v_stop_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
size_t v_i_boxed_1385_; size_t v_stop_boxed_1386_; lean_object* v_res_1387_; 
v_i_boxed_1385_ = lean_unbox_usize(v_i_1376_);
lean_dec(v_i_1376_);
v_stop_boxed_1386_ = lean_unbox_usize(v_stop_1377_);
lean_dec(v_stop_1377_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_as_1375_, v_i_boxed_1385_, v_stop_boxed_1386_, v_b_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v_as_1375_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(lean_object* v_init_1388_, lean_object* v_includeDelayed_1389_, lean_object* v___y_1390_, lean_object* v_as_1391_, lean_object* v_sz_1392_, lean_object* v_i_1393_, lean_object* v_b_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
uint8_t v_includeDelayed_boxed_1401_; uint8_t v___y_17229__boxed_1402_; size_t v_sz_boxed_1403_; size_t v_i_boxed_1404_; lean_object* v_res_1405_; 
v_includeDelayed_boxed_1401_ = lean_unbox(v_includeDelayed_1389_);
v___y_17229__boxed_1402_ = lean_unbox(v___y_1390_);
v_sz_boxed_1403_ = lean_unbox_usize(v_sz_1392_);
lean_dec(v_sz_1392_);
v_i_boxed_1404_ = lean_unbox_usize(v_i_1393_);
lean_dec(v_i_1393_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_1388_, v_includeDelayed_boxed_1401_, v___y_17229__boxed_1402_, v_as_1391_, v_sz_boxed_1403_, v_i_boxed_1404_, v_b_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v_as_1391_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(lean_object* v_includeDelayed_1406_, lean_object* v___y_1407_, lean_object* v_t_1408_, lean_object* v_init_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v_includeDelayed_boxed_1416_; uint8_t v___y_17252__boxed_1417_; lean_object* v_res_1418_; 
v_includeDelayed_boxed_1416_ = lean_unbox(v_includeDelayed_1406_);
v___y_17252__boxed_1417_ = lean_unbox(v___y_1407_);
v_res_1418_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_boxed_1416_, v___y_17252__boxed_1417_, v_t_1408_, v_init_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v_t_1408_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object* v_includeDelayed_1419_, lean_object* v___y_1420_, lean_object* v_as_1421_, lean_object* v_sz_1422_, lean_object* v_i_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v_includeDelayed_boxed_1431_; uint8_t v___y_17276__boxed_1432_; size_t v_sz_boxed_1433_; size_t v_i_boxed_1434_; lean_object* v_res_1435_; 
v_includeDelayed_boxed_1431_ = lean_unbox(v_includeDelayed_1419_);
v___y_17276__boxed_1432_ = lean_unbox(v___y_1420_);
v_sz_boxed_1433_ = lean_unbox_usize(v_sz_1422_);
lean_dec(v_sz_1422_);
v_i_boxed_1434_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_boxed_1431_, v___y_17276__boxed_1432_, v_as_1421_, v_sz_boxed_1433_, v_i_boxed_1434_, v_b_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v_as_1421_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object* v_includeDelayed_1436_, lean_object* v___y_1437_, lean_object* v_as_1438_, lean_object* v_sz_1439_, lean_object* v_i_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v_includeDelayed_boxed_1448_; uint8_t v___y_17305__boxed_1449_; size_t v_sz_boxed_1450_; size_t v_i_boxed_1451_; lean_object* v_res_1452_; 
v_includeDelayed_boxed_1448_ = lean_unbox(v_includeDelayed_1436_);
v___y_17305__boxed_1449_ = lean_unbox(v___y_1437_);
v_sz_boxed_1450_ = lean_unbox_usize(v_sz_1439_);
lean_dec(v_sz_1439_);
v_i_boxed_1451_ = lean_unbox_usize(v_i_1440_);
lean_dec(v_i_1440_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_boxed_1448_, v___y_17305__boxed_1449_, v_as_1438_, v_sz_boxed_1450_, v_i_boxed_1451_, v_b_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v_as_1438_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object* v_includeDelayed_1453_, lean_object* v___y_1454_, lean_object* v_as_1455_, lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v_includeDelayed_boxed_1465_; uint8_t v___y_17334__boxed_1466_; size_t v_sz_boxed_1467_; size_t v_i_boxed_1468_; lean_object* v_res_1469_; 
v_includeDelayed_boxed_1465_ = lean_unbox(v_includeDelayed_1453_);
v___y_17334__boxed_1466_ = lean_unbox(v___y_1454_);
v_sz_boxed_1467_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1468_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_boxed_1465_, v___y_17334__boxed_1466_, v_as_1455_, v_sz_boxed_1467_, v_i_boxed_1468_, v_b_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v_as_1455_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object* v_includeDelayed_1470_, lean_object* v___y_1471_, lean_object* v_as_1472_, lean_object* v_sz_1473_, lean_object* v_i_1474_, lean_object* v_b_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_includeDelayed_boxed_1482_; uint8_t v___y_17363__boxed_1483_; size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_includeDelayed_boxed_1482_ = lean_unbox(v_includeDelayed_1470_);
v___y_17363__boxed_1483_ = lean_unbox(v___y_1471_);
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1473_);
lean_dec(v_sz_1473_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1474_);
lean_dec(v_i_1474_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_boxed_1482_, v___y_17363__boxed_1483_, v_as_1472_, v_sz_boxed_1484_, v_i_boxed_1485_, v_b_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v_as_1472_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object* v_init_1487_, lean_object* v_includeDelayed_1488_, lean_object* v___y_1489_, lean_object* v_n_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v_includeDelayed_boxed_1498_; uint8_t v___y_17392__boxed_1499_; lean_object* v_res_1500_; 
v_includeDelayed_boxed_1498_ = lean_unbox(v_includeDelayed_1488_);
v___y_17392__boxed_1499_ = lean_unbox(v___y_1489_);
v_res_1500_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1487_, v_includeDelayed_boxed_1498_, v___y_17392__boxed_1499_, v_n_1490_, v_b_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v_n_1490_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object* v_e_1501_, lean_object* v_includeDelayed_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
uint8_t v_includeDelayed_boxed_1509_; lean_object* v_res_1510_; 
v_includeDelayed_boxed_1509_ = lean_unbox(v_includeDelayed_1502_);
v_res_1510_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1501_, v_includeDelayed_boxed_1509_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go___boxed(lean_object* v_mvarId_1511_, lean_object* v_includeDelayed_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
uint8_t v_includeDelayed_boxed_1519_; lean_object* v_res_1520_; 
v_includeDelayed_boxed_1519_ = lean_unbox(v_includeDelayed_1512_);
v_res_1520_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1511_, v_includeDelayed_boxed_1519_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(lean_object* v_mvarId_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1521_, v___y_1524_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(lean_object* v_mvarId_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(v_mvarId_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec(v_mvarId_1529_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_object* v_00_u03b1_1537_, lean_object* v_ref_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1538_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(lean_object* v_00_u03b1_1546_, lean_object* v_ref_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(v_00_u03b1_1546_, v_ref_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(lean_object* v_00_u03b2_1555_, lean_object* v_m_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_1556_, v_a_1557_, v_b_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(lean_object* v_mvarId_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_1560_, v___y_1563_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(lean_object* v_mvarId_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_mvarId_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v_mvarId_1568_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(lean_object* v_mvarId_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_1576_, v___y_1579_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(lean_object* v_mvarId_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec(v_mvarId_1584_);
return v_res_1591_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_object* v_00_u03b2_1592_, lean_object* v_a_1593_, lean_object* v_x_1594_){
_start:
{
uint8_t v___x_1595_; 
v___x_1595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_1593_, v_x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1596_, lean_object* v_a_1597_, lean_object* v_x_1598_){
_start:
{
uint8_t v_res_1599_; lean_object* v_r_1600_; 
v_res_1599_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(v_00_u03b2_1596_, v_a_1597_, v_x_1598_);
lean_dec(v_x_1598_);
lean_dec(v_a_1597_);
v_r_1600_ = lean_box(v_res_1599_);
return v_r_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1(lean_object* v_00_u03b2_1601_, lean_object* v_data_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_data_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1604_, lean_object* v_i_1605_, lean_object* v_source_1606_, lean_object* v_target_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v_i_1605_, v_source_1606_, v_target_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_x_1610_, v_x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies(lean_object* v_mvarId_1613_, uint8_t v_includeDelayed_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1621_ = lean_st_mk_ref(v___x_1620_);
lean_inc_ref(v_a_1617_);
v___x_1622_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1613_, v_includeDelayed_1614_, v___x_1621_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1630_; 
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v___x_1622_, 0);
lean_dec(v_unused_1631_);
v___x_1624_ = v___x_1622_;
v_isShared_1625_ = v_isSharedCheck_1630_;
goto v_resetjp_1623_;
}
else
{
lean_dec(v___x_1622_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1630_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_st_ref_get(v___x_1621_);
lean_dec(v___x_1621_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1626_);
v___x_1628_ = v___x_1624_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v___x_1621_);
v_a_1632_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1622_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1622_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object* v_mvarId_1640_, lean_object* v_includeDelayed_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
uint8_t v_includeDelayed_boxed_1647_; lean_object* v_res_1648_; 
v_includeDelayed_boxed_1647_ = lean_unbox(v_includeDelayed_1641_);
v_res_1648_ = l_Lean_MVarId_getMVarDependencies(v_mvarId_1640_, v_includeDelayed_boxed_1647_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies(lean_object* v_e_1649_, uint8_t v_includeDelayed_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1657_ = lean_st_mk_ref(v___x_1656_);
v___x_1658_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1649_, v_includeDelayed_1650_, v___x_1657_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v___x_1658_, 0);
lean_dec(v_unused_1667_);
v___x_1660_ = v___x_1658_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_dec(v___x_1658_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_st_ref_get(v___x_1657_);
lean_dec(v___x_1657_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v___x_1657_);
v_a_1668_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1658_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1658_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies___boxed(lean_object* v_e_1676_, lean_object* v_includeDelayed_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
uint8_t v_includeDelayed_boxed_1683_; lean_object* v_res_1684_; 
v_includeDelayed_boxed_1683_ = lean_unbox(v_includeDelayed_1677_);
v_res_1684_ = l_Lean_Expr_getMVarDependencies(v_e_1676_, v_includeDelayed_boxed_1683_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
return v_res_1684_;
}
}
lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
