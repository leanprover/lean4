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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1;
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
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
lean_dec_ref(v___x_80_);
v___x_82_ = lean_st_ref_get(v_a_74_);
v_result_83_ = lean_ctor_get(v___x_82_, 1);
lean_inc_ref(v_result_83_);
v___x_84_ = l_Lean_Expr_collectMVars(v___x_82_, v_a_81_);
lean_inc_ref(v___x_84_);
v___x_85_ = lean_st_ref_set(v_a_74_, v___x_84_);
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
lean_dec_ref(v___x_130_);
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
lean_dec_ref(v_a_131_);
v_mvarIdPending_139_ = lean_ctor_get(v_val_138_, 1);
lean_inc(v_mvarIdPending_139_);
lean_dec(v_val_138_);
v___x_140_ = l_Lean_mkMVar(v_mvarIdPending_139_);
v___x_141_ = l_Lean_Meta_collectMVars(v___x_140_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_dec_ref(v___x_141_);
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
return v___x_245_;
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; 
v___x_254_ = ((size_t)5ULL);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_shift_left(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; 
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_259_ = lean_usize_sub(v___x_258_, v___x_257_);
return v___x_259_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_260_, size_t v_x_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v_es_263_; lean_object* v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v_j_268_; lean_object* v___x_269_; 
v_es_263_ = lean_ctor_get(v_x_260_, 0);
v___x_264_ = lean_box(2);
v___x_265_ = ((size_t)5ULL);
v___x_266_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_267_ = lean_usize_land(v_x_261_, v___x_266_);
v_j_268_ = lean_usize_to_nat(v___x_267_);
v___x_269_ = lean_array_get_borrowed(v___x_264_, v_es_263_, v_j_268_);
lean_dec(v_j_268_);
switch(lean_obj_tag(v___x_269_))
{
case 0:
{
lean_object* v_key_270_; uint8_t v___x_271_; 
v_key_270_ = lean_ctor_get(v___x_269_, 0);
v___x_271_ = l_Lean_instBEqMVarId_beq(v_x_262_, v_key_270_);
return v___x_271_;
}
case 1:
{
lean_object* v_node_272_; size_t v___x_273_; 
v_node_272_ = lean_ctor_get(v___x_269_, 0);
v___x_273_ = lean_usize_shift_right(v_x_261_, v___x_265_);
v_x_260_ = v_node_272_;
v_x_261_ = v___x_273_;
goto _start;
}
default: 
{
uint8_t v___x_275_; 
v___x_275_ = 0;
return v___x_275_;
}
}
}
else
{
lean_object* v_ks_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_ks_276_ = lean_ctor_get(v_x_260_, 0);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_276_, v___x_277_, v_x_262_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
size_t v_x_1309__boxed_282_; uint8_t v_res_283_; lean_object* v_r_284_; 
v_x_1309__boxed_282_ = lean_unbox_usize(v_x_280_);
lean_dec(v_x_280_);
v_res_283_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_279_, v_x_1309__boxed_282_, v_x_281_);
lean_dec(v_x_281_);
lean_dec_ref(v_x_279_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
uint64_t v___x_287_; size_t v___x_288_; uint8_t v___x_289_; 
v___x_287_ = l_Lean_instHashableMVarId_hash(v_x_286_);
v___x_288_ = lean_uint64_to_usize(v___x_287_);
v___x_289_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_285_, v___x_288_, v_x_286_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg___boxed(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_290_, v_x_291_);
lean_dec(v_x_291_);
lean_dec_ref(v_x_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(lean_object* v_mvarId_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_mctx_298_; lean_object* v_dAssignment_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_297_ = lean_st_ref_get(v___y_295_);
v_mctx_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_mctx_298_);
lean_dec(v___x_297_);
v_dAssignment_299_ = lean_ctor_get(v_mctx_298_, 9);
lean_inc_ref(v_dAssignment_299_);
lean_dec_ref(v_mctx_298_);
v___x_300_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_299_, v_mvarId_294_);
lean_dec_ref(v_dAssignment_299_);
v___x_301_ = lean_box(v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(lean_object* v_mvarId_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec(v_mvarId_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(lean_object* v_as_307_, size_t v_i_308_, size_t v_stop_309_, lean_object* v_b_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_a_317_; uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_eq(v_i_308_, v_stop_309_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_325_; 
v___x_322_ = lean_array_uget_borrowed(v_as_307_, v_i_308_);
v___x_325_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v___x_322_, v___y_312_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; uint8_t v___x_327_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref(v___x_325_);
v___x_327_ = lean_unbox(v_a_326_);
lean_dec(v_a_326_);
if (v___x_327_ == 0)
{
goto v___jp_323_;
}
else
{
v_a_317_ = v_b_310_;
goto v___jp_316_;
}
}
else
{
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_328_; uint8_t v___x_329_; 
v_a_328_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_328_);
lean_dec_ref(v___x_325_);
v___x_329_ = lean_unbox(v_a_328_);
lean_dec(v_a_328_);
if (v___x_329_ == 0)
{
v_a_317_ = v_b_310_;
goto v___jp_316_;
}
else
{
goto v___jp_323_;
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_b_310_);
v_a_330_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_325_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_325_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
v___jp_323_:
{
lean_object* v___x_324_; 
lean_inc(v___x_322_);
v___x_324_ = lean_array_push(v_b_310_, v___x_322_);
v_a_317_ = v___x_324_;
goto v___jp_316_;
}
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_b_310_);
return v___x_338_;
}
v___jp_316_:
{
size_t v___x_318_; size_t v___x_319_; 
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_308_, v___x_318_);
v_i_308_ = v___x_319_;
v_b_310_ = v_a_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1___boxed(lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_stop_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
size_t v_i_boxed_348_; size_t v_stop_boxed_349_; lean_object* v_res_350_; 
v_i_boxed_348_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_stop_boxed_349_ = lean_unbox_usize(v_stop_341_);
lean_dec(v_stop_341_);
v_res_350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_339_, v_i_boxed_348_, v_stop_boxed_349_, v_b_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec_ref(v_as_339_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object* v_e_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_getMVars(v_e_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_379_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_379_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_379_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_379_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_array_get_size(v_a_358_);
v___x_364_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_365_ = lean_nat_dec_lt(v___x_362_, v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v___x_367_; 
lean_dec(v_a_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_364_);
v___x_367_ = v___x_360_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_364_);
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
uint8_t v___x_369_; 
v___x_369_ = lean_nat_dec_le(v___x_363_, v___x_363_);
if (v___x_369_ == 0)
{
if (v___x_365_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_a_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_364_);
v___x_371_ = v___x_360_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_364_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
lean_del_object(v___x_360_);
v___x_373_ = ((size_t)0ULL);
v___x_374_ = lean_usize_of_nat(v___x_363_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_358_, v___x_373_, v___x_374_, v___x_364_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_358_);
return v___x_375_;
}
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
lean_del_object(v___x_360_);
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_363_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_358_, v___x_376_, v___x_377_, v___x_364_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_358_);
return v___x_378_;
}
}
}
}
else
{
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object* v_e_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_getMVarsNoDelayed(v_e_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(lean_object* v_mvarId_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_387_, v___y_389_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(lean_object* v_mvarId_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(v_mvarId_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v_mvarId_394_);
return v_res_400_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(lean_object* v_00_u03b2_401_, lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_402_, v_x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(v_00_u03b2_405_, v_x_406_, v_x_407_);
lean_dec(v_x_407_);
lean_dec_ref(v_x_406_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_410_, lean_object* v_x_411_, size_t v_x_412_, lean_object* v_x_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_411_, v_x_412_, v_x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_415_, lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
size_t v_x_1520__boxed_419_; uint8_t v_res_420_; lean_object* v_r_421_; 
v_x_1520__boxed_419_ = lean_unbox_usize(v_x_417_);
lean_dec(v_x_417_);
v_res_420_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(v_00_u03b2_415_, v_x_416_, v_x_1520__boxed_419_, v_x_418_);
lean_dec(v_x_418_);
lean_dec_ref(v_x_416_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_422_, lean_object* v_keys_423_, lean_object* v_vals_424_, lean_object* v_heq_425_, lean_object* v_i_426_, lean_object* v_k_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_423_, v_i_426_, v_k_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_429_, lean_object* v_keys_430_, lean_object* v_vals_431_, lean_object* v_heq_432_, lean_object* v_i_433_, lean_object* v_k_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_429_, v_keys_430_, v_vals_431_, v_heq_432_, v_i_433_, v_k_434_);
lean_dec(v_k_434_);
lean_dec_ref(v_vals_431_);
lean_dec_ref(v_keys_430_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v_x_437_);
return v___x_445_;
}
else
{
lean_object* v_head_446_; lean_object* v_tail_447_; lean_object* v_type_448_; lean_object* v___x_449_; 
v_head_446_ = lean_ctor_get(v_x_438_, 0);
lean_inc(v_head_446_);
v_tail_447_ = lean_ctor_get(v_x_438_, 1);
lean_inc(v_tail_447_);
lean_dec_ref(v_x_438_);
v_type_448_ = lean_ctor_get(v_head_446_, 1);
lean_inc_ref(v_type_448_);
lean_dec(v_head_446_);
v___x_449_ = l_Lean_Meta_collectMVars(v_type_448_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_449_);
v_x_437_ = v_a_450_;
v_x_438_ = v_tail_447_;
goto _start;
}
else
{
lean_dec(v_tail_447_);
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_452_, v_x_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_x_461_);
return v___x_469_;
}
else
{
lean_object* v_head_470_; lean_object* v_tail_471_; lean_object* v___y_473_; lean_object* v_type_476_; lean_object* v_ctors_477_; lean_object* v___x_478_; 
v_head_470_ = lean_ctor_get(v_x_462_, 0);
lean_inc(v_head_470_);
v_tail_471_ = lean_ctor_get(v_x_462_, 1);
lean_inc(v_tail_471_);
lean_dec_ref(v_x_462_);
v_type_476_ = lean_ctor_get(v_head_470_, 1);
lean_inc_ref(v_type_476_);
v_ctors_477_ = lean_ctor_get(v_head_470_, 2);
lean_inc(v_ctors_477_);
lean_dec(v_head_470_);
v___x_478_ = l_Lean_Meta_collectMVars(v_type_476_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref(v___x_478_);
v___x_480_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_a_479_, v_ctors_477_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
v___y_473_ = v___x_480_;
goto v___jp_472_;
}
else
{
lean_dec(v_ctors_477_);
v___y_473_ = v___x_478_;
goto v___jp_472_;
}
v___jp_472_:
{
if (lean_obj_tag(v___y_473_) == 0)
{
lean_object* v_a_474_; 
v_a_474_ = lean_ctor_get(v___y_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___y_473_);
v_x_461_ = v_a_474_;
v_x_462_ = v_tail_471_;
goto _start;
}
else
{
lean_dec(v_tail_471_);
return v___y_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_481_, v_x_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_x_490_);
return v___x_498_;
}
else
{
lean_object* v_head_499_; lean_object* v_tail_500_; lean_object* v___y_502_; lean_object* v_toConstantVal_505_; lean_object* v_value_506_; lean_object* v_type_507_; lean_object* v___x_508_; 
v_head_499_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_head_499_);
v_tail_500_ = lean_ctor_get(v_x_491_, 1);
lean_inc(v_tail_500_);
lean_dec_ref(v_x_491_);
v_toConstantVal_505_ = lean_ctor_get(v_head_499_, 0);
lean_inc_ref(v_toConstantVal_505_);
v_value_506_ = lean_ctor_get(v_head_499_, 1);
lean_inc_ref(v_value_506_);
lean_dec(v_head_499_);
v_type_507_ = lean_ctor_get(v_toConstantVal_505_, 2);
lean_inc_ref(v_type_507_);
lean_dec_ref(v_toConstantVal_505_);
v___x_508_ = l_Lean_Meta_collectMVars(v_type_507_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v___x_508_);
v___x_509_ = l_Lean_Meta_collectMVars(v_value_506_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
v___y_502_ = v___x_509_;
goto v___jp_501_;
}
else
{
lean_dec_ref(v_value_506_);
v___y_502_ = v___x_508_;
goto v___jp_501_;
}
v___jp_501_:
{
if (lean_obj_tag(v___y_502_) == 0)
{
lean_object* v_a_503_; 
v_a_503_ = lean_ctor_get(v___y_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___y_502_);
v_x_490_ = v_a_503_;
v_x_491_ = v_tail_500_;
goto _start;
}
else
{
lean_dec(v_tail_500_);
return v___y_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_510_, v_x_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(lean_object* v_d_519_, lean_object* v_a_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
switch(lean_obj_tag(v_d_519_))
{
case 0:
{
lean_object* v_val_527_; lean_object* v_toConstantVal_528_; lean_object* v_type_529_; lean_object* v___x_530_; 
v_val_527_ = lean_ctor_get(v_d_519_, 0);
lean_inc_ref(v_val_527_);
lean_dec_ref(v_d_519_);
v_toConstantVal_528_ = lean_ctor_get(v_val_527_, 0);
lean_inc_ref(v_toConstantVal_528_);
lean_dec_ref(v_val_527_);
v_type_529_ = lean_ctor_get(v_toConstantVal_528_, 2);
lean_inc_ref(v_type_529_);
lean_dec_ref(v_toConstantVal_528_);
v___x_530_ = l_Lean_Meta_collectMVars(v_type_529_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
return v___x_530_;
}
case 4:
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_a_520_);
return v___x_531_;
}
case 5:
{
lean_object* v_defns_532_; lean_object* v___x_533_; 
v_defns_532_ = lean_ctor_get(v_d_519_, 0);
lean_inc(v_defns_532_);
lean_dec_ref(v_d_519_);
v___x_533_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_a_520_, v_defns_532_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
return v___x_533_;
}
case 6:
{
lean_object* v_types_534_; lean_object* v___x_535_; 
v_types_534_ = lean_ctor_get(v_d_519_, 2);
lean_inc(v_types_534_);
lean_dec_ref(v_d_519_);
v___x_535_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_a_520_, v_types_534_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
return v___x_535_;
}
default: 
{
lean_object* v_val_536_; lean_object* v_toConstantVal_537_; lean_object* v_value_538_; lean_object* v_type_539_; lean_object* v___x_540_; 
v_val_536_ = lean_ctor_get(v_d_519_, 0);
lean_inc_ref(v_val_536_);
lean_dec(v_d_519_);
v_toConstantVal_537_ = lean_ctor_get(v_val_536_, 0);
lean_inc_ref(v_toConstantVal_537_);
v_value_538_ = lean_ctor_get(v_val_536_, 1);
lean_inc_ref(v_value_538_);
lean_dec_ref(v_val_536_);
v_type_539_ = lean_ctor_get(v_toConstantVal_537_, 2);
lean_inc_ref(v_type_539_);
lean_dec_ref(v_toConstantVal_537_);
v___x_540_ = l_Lean_Meta_collectMVars(v_type_539_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_541_; 
lean_dec_ref(v___x_540_);
v___x_541_ = l_Lean_Meta_collectMVars(v_value_538_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
return v___x_541_;
}
else
{
lean_dec_ref(v_value_538_);
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(lean_object* v_d_542_, lean_object* v_a_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_542_, v_a_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object* v_d_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_box(0);
v___x_559_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_551_, v___x_558_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object* v_d_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_collectMVarsAtDecl(v_d_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object* v_d_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_575_ = lean_st_mk_ref(v___x_574_);
v___x_576_ = l_Lean_Meta_collectMVarsAtDecl(v_d_568_, v___x_575_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_585_; 
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; 
v_unused_586_ = lean_ctor_get(v___x_576_, 0);
lean_dec(v_unused_586_);
v___x_578_ = v___x_576_;
v_isShared_579_ = v_isSharedCheck_585_;
goto v_resetjp_577_;
}
else
{
lean_dec(v___x_576_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_585_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v_result_581_; lean_object* v___x_583_; 
v___x_580_ = lean_st_ref_get(v___x_575_);
lean_dec(v___x_575_);
v_result_581_ = lean_ctor_get(v___x_580_, 1);
lean_inc_ref(v_result_581_);
lean_dec(v___x_580_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_result_581_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_result_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v___x_575_);
v_a_587_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_576_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_576_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object* v_d_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_getMVarsAtDecl(v_d_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(lean_object* v_mvarId_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v_mctx_606_; lean_object* v_dAssignment_607_; uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_605_ = lean_st_ref_get(v___y_603_);
v_mctx_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc_ref(v_mctx_606_);
lean_dec(v___x_605_);
v_dAssignment_607_ = lean_ctor_get(v_mctx_606_, 9);
lean_inc_ref(v_dAssignment_607_);
lean_dec_ref(v_mctx_606_);
v___x_608_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_607_, v_mvarId_602_);
lean_dec_ref(v_dAssignment_607_);
v___x_609_ = lean_box(v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(lean_object* v_mvarId_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec(v_mvarId_611_);
return v_res_614_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(lean_object* v_a_615_, lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
else
{
lean_object* v_key_618_; lean_object* v_tail_619_; uint8_t v___x_620_; 
v_key_618_ = lean_ctor_get(v_x_616_, 0);
v_tail_619_ = lean_ctor_get(v_x_616_, 2);
v___x_620_ = l_Lean_instBEqMVarId_beq(v_key_618_, v_a_615_);
if (v___x_620_ == 0)
{
v_x_616_ = v_tail_619_;
goto _start;
}
else
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_622_, lean_object* v_x_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_622_, v_x_623_);
lean_dec(v_x_623_);
lean_dec(v_a_622_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
return v_x_626_;
}
else
{
lean_object* v_key_628_; lean_object* v_value_629_; lean_object* v_tail_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_653_; 
v_key_628_ = lean_ctor_get(v_x_627_, 0);
v_value_629_ = lean_ctor_get(v_x_627_, 1);
v_tail_630_ = lean_ctor_get(v_x_627_, 2);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_627_);
if (v_isSharedCheck_653_ == 0)
{
v___x_632_ = v_x_627_;
v_isShared_633_ = v_isSharedCheck_653_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_tail_630_);
lean_inc(v_value_629_);
lean_inc(v_key_628_);
lean_dec(v_x_627_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_653_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; uint64_t v___x_635_; uint64_t v___x_636_; uint64_t v___x_637_; uint64_t v_fold_638_; uint64_t v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; size_t v___x_642_; size_t v___x_643_; size_t v___x_644_; size_t v___x_645_; size_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_634_ = lean_array_get_size(v_x_626_);
v___x_635_ = l_Lean_instHashableMVarId_hash(v_key_628_);
v___x_636_ = 32ULL;
v___x_637_ = lean_uint64_shift_right(v___x_635_, v___x_636_);
v_fold_638_ = lean_uint64_xor(v___x_635_, v___x_637_);
v___x_639_ = 16ULL;
v___x_640_ = lean_uint64_shift_right(v_fold_638_, v___x_639_);
v___x_641_ = lean_uint64_xor(v_fold_638_, v___x_640_);
v___x_642_ = lean_uint64_to_usize(v___x_641_);
v___x_643_ = lean_usize_of_nat(v___x_634_);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_sub(v___x_643_, v___x_644_);
v___x_646_ = lean_usize_land(v___x_642_, v___x_645_);
v___x_647_ = lean_array_uget_borrowed(v_x_626_, v___x_646_);
lean_inc(v___x_647_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 2, v___x_647_);
v___x_649_ = v___x_632_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_key_628_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_value_629_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v___x_647_);
v___x_649_ = v_reuseFailAlloc_652_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; 
v___x_650_ = lean_array_uset(v_x_626_, v___x_646_, v___x_649_);
v_x_626_ = v___x_650_;
v_x_627_ = v_tail_630_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(lean_object* v_i_654_, lean_object* v_source_655_, lean_object* v_target_656_){
_start:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_array_get_size(v_source_655_);
v___x_658_ = lean_nat_dec_lt(v_i_654_, v___x_657_);
if (v___x_658_ == 0)
{
lean_dec_ref(v_source_655_);
lean_dec(v_i_654_);
return v_target_656_;
}
else
{
lean_object* v_es_659_; lean_object* v___x_660_; lean_object* v_source_661_; lean_object* v_target_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_es_659_ = lean_array_fget(v_source_655_, v_i_654_);
v___x_660_ = lean_box(0);
v_source_661_ = lean_array_fset(v_source_655_, v_i_654_, v___x_660_);
v_target_662_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_target_656_, v_es_659_);
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_add(v_i_654_, v___x_663_);
lean_dec(v_i_654_);
v_i_654_ = v___x_664_;
v_source_655_ = v_source_661_;
v_target_656_ = v_target_662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(lean_object* v_data_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_nbuckets_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_667_ = lean_array_get_size(v_data_666_);
v___x_668_ = lean_unsigned_to_nat(2u);
v_nbuckets_669_ = lean_nat_mul(v___x_667_, v___x_668_);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_box(0);
v___x_672_ = lean_mk_array(v_nbuckets_669_, v___x_671_);
v___x_673_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v___x_670_, v_data_666_, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(lean_object* v_m_674_, lean_object* v_a_675_, lean_object* v_b_676_){
_start:
{
lean_object* v_size_677_; lean_object* v_buckets_678_; lean_object* v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v_fold_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v_bkt_692_; uint8_t v___x_693_; 
v_size_677_ = lean_ctor_get(v_m_674_, 0);
v_buckets_678_ = lean_ctor_get(v_m_674_, 1);
v___x_679_ = lean_array_get_size(v_buckets_678_);
v___x_680_ = l_Lean_instHashableMVarId_hash(v_a_675_);
v___x_681_ = 32ULL;
v___x_682_ = lean_uint64_shift_right(v___x_680_, v___x_681_);
v_fold_683_ = lean_uint64_xor(v___x_680_, v___x_682_);
v___x_684_ = 16ULL;
v___x_685_ = lean_uint64_shift_right(v_fold_683_, v___x_684_);
v___x_686_ = lean_uint64_xor(v_fold_683_, v___x_685_);
v___x_687_ = lean_uint64_to_usize(v___x_686_);
v___x_688_ = lean_usize_of_nat(v___x_679_);
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_sub(v___x_688_, v___x_689_);
v___x_691_ = lean_usize_land(v___x_687_, v___x_690_);
v_bkt_692_ = lean_array_uget_borrowed(v_buckets_678_, v___x_691_);
v___x_693_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_675_, v_bkt_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_714_; 
lean_inc_ref(v_buckets_678_);
lean_inc(v_size_677_);
v_isSharedCheck_714_ = !lean_is_exclusive(v_m_674_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_715_ = lean_ctor_get(v_m_674_, 1);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_m_674_, 0);
lean_dec(v_unused_716_);
v___x_695_ = v_m_674_;
v_isShared_696_ = v_isSharedCheck_714_;
goto v_resetjp_694_;
}
else
{
lean_dec(v_m_674_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_714_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v_size_x27_698_; lean_object* v___x_699_; lean_object* v_buckets_x27_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v_size_x27_698_ = lean_nat_add(v_size_677_, v___x_697_);
lean_dec(v_size_677_);
lean_inc(v_bkt_692_);
v___x_699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_699_, 0, v_a_675_);
lean_ctor_set(v___x_699_, 1, v_b_676_);
lean_ctor_set(v___x_699_, 2, v_bkt_692_);
v_buckets_x27_700_ = lean_array_uset(v_buckets_678_, v___x_691_, v___x_699_);
v___x_701_ = lean_unsigned_to_nat(4u);
v___x_702_ = lean_nat_mul(v_size_x27_698_, v___x_701_);
v___x_703_ = lean_unsigned_to_nat(3u);
v___x_704_ = lean_nat_div(v___x_702_, v___x_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_array_get_size(v_buckets_x27_700_);
v___x_706_ = lean_nat_dec_le(v___x_704_, v___x_705_);
lean_dec(v___x_704_);
if (v___x_706_ == 0)
{
lean_object* v_val_707_; lean_object* v___x_709_; 
v_val_707_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_buckets_x27_700_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_val_707_);
lean_ctor_set(v___x_695_, 0, v_size_x27_698_);
v___x_709_ = v___x_695_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_size_x27_698_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_val_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v___x_712_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_buckets_x27_700_);
lean_ctor_set(v___x_695_, 0, v_size_x27_698_);
v___x_712_ = v___x_695_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_size_x27_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_buckets_x27_700_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_dec(v_b_676_);
lean_dec(v_a_675_);
return v_m_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(uint8_t v_includeDelayed_717_, lean_object* v_as_718_, size_t v_sz_719_, size_t v_i_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_a_729_; uint8_t v___x_733_; 
v___x_733_ = lean_usize_dec_lt(v_i_720_, v_sz_719_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v_b_721_);
return v___x_734_;
}
else
{
lean_object* v_a_735_; 
v_a_735_ = lean_array_uget_borrowed(v_as_718_, v_i_720_);
if (v_includeDelayed_717_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_a_735_, v___y_724_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; uint8_t v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref(v___x_739_);
v___x_741_ = lean_unbox(v_a_740_);
lean_dec(v_a_740_);
if (v___x_741_ == 0)
{
goto v___jp_736_;
}
else
{
v_a_729_ = v_b_721_;
goto v___jp_728_;
}
}
else
{
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_742_; uint8_t v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_742_);
lean_dec_ref(v___x_739_);
v___x_743_ = lean_unbox(v_a_742_);
lean_dec(v_a_742_);
if (v___x_743_ == 0)
{
v_a_729_ = v_b_721_;
goto v___jp_728_;
}
else
{
goto v___jp_736_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_b_721_);
v_a_744_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_739_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_739_);
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
goto v___jp_736_;
}
v___jp_736_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_box(0);
lean_inc(v_a_735_);
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_b_721_, v_a_735_, v___x_737_);
v_a_729_ = v___x_738_;
goto v___jp_728_;
}
}
v___jp_728_:
{
size_t v___x_730_; size_t v___x_731_; 
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_720_, v___x_730_);
v_i_720_ = v___x_731_;
v_b_721_ = v_a_729_;
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
lean_dec_ref(v___x_829_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(lean_object* v_init_874_, uint8_t v_includeDelayed_875_, lean_object* v_as_876_, size_t v_sz_877_, size_t v_i_878_, lean_object* v_b_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = lean_usize_dec_lt(v_i_878_, v_sz_877_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_b_879_);
return v___x_887_;
}
else
{
lean_object* v_snd_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_922_; 
v_snd_888_ = lean_ctor_get(v_b_879_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_b_879_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_b_879_, 0);
lean_dec(v_unused_923_);
v___x_890_ = v_b_879_;
v_isShared_891_ = v_isSharedCheck_922_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_snd_888_);
lean_dec(v_b_879_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_922_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_a_892_; lean_object* v___x_893_; 
v_a_892_ = lean_array_uget_borrowed(v_as_876_, v_i_878_);
lean_inc(v_snd_888_);
lean_inc(v_a_892_);
v___x_893_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_874_, v_includeDelayed_875_, v_a_892_, v_snd_888_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_913_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_913_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_913_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_913_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
if (lean_obj_tag(v_a_894_) == 0)
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_a_894_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_898_);
v___x_900_ = v___x_890_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_snd_888_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_900_);
v___x_902_ = v___x_896_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
lean_del_object(v___x_896_);
lean_dec(v_snd_888_);
v_a_905_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v_a_894_);
v___x_906_ = lean_box(0);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v_a_905_);
lean_ctor_set(v___x_890_, 0, v___x_906_);
v___x_908_ = v___x_890_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_a_905_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
size_t v___x_909_; size_t v___x_910_; 
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_878_, v___x_909_);
v_i_878_ = v___x_910_;
v_b_879_ = v___x_908_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_del_object(v___x_890_);
lean_dec(v_snd_888_);
v_a_914_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_893_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_893_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(uint8_t v_includeDelayed_924_, lean_object* v_as_925_, size_t v_sz_926_, size_t v_i_927_, lean_object* v_b_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_lt(v_i_927_, v_sz_926_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_b_928_);
return v___x_936_;
}
else
{
lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_975_; 
v_snd_937_ = lean_ctor_get(v_b_928_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_b_928_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v_b_928_, 0);
lean_dec(v_unused_976_);
v___x_939_ = v_b_928_;
v_isShared_940_ = v_isSharedCheck_975_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_dec(v_b_928_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_975_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v_a_943_; lean_object* v_a_950_; 
v___x_941_ = lean_box(0);
v_a_950_ = lean_array_uget_borrowed(v_as_925_, v_i_927_);
if (lean_obj_tag(v_a_950_) == 0)
{
v_a_943_ = v_snd_937_;
goto v___jp_942_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v_snd_937_);
v_val_951_ = lean_ctor_get(v_a_950_, 0);
v___x_952_ = l_Lean_LocalDecl_type(v_val_951_);
v___x_953_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_952_, v_includeDelayed_924_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; 
lean_dec_ref(v___x_953_);
v___x_954_ = lean_box(0);
v___x_955_ = 0;
v___x_956_ = l_Lean_LocalDecl_value_x3f(v_val_951_, v___x_955_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_958_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_957_, v_includeDelayed_924_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_dec_ref(v___x_958_);
v_a_943_ = v___x_954_;
goto v___jp_942_;
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_del_object(v___x_939_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_dec(v___x_956_);
v_a_943_ = v___x_954_;
goto v___jp_942_;
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_del_object(v___x_939_);
v_a_967_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_953_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_953_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
v___jp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v_a_943_);
lean_ctor_set(v___x_939_, 0, v___x_941_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_a_943_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
size_t v___x_946_; size_t v___x_947_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_927_, v___x_946_);
v_i_927_ = v___x_947_;
v_b_928_ = v___x_945_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(uint8_t v_includeDelayed_977_, lean_object* v_as_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_b_981_);
return v___x_989_;
}
else
{
lean_object* v_snd_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1028_; 
v_snd_990_ = lean_ctor_get(v_b_981_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_b_981_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_b_981_, 0);
lean_dec(v_unused_1029_);
v___x_992_ = v_b_981_;
v_isShared_993_ = v_isSharedCheck_1028_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_snd_990_);
lean_dec(v_b_981_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1028_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v_a_996_; lean_object* v_a_1003_; 
v___x_994_ = lean_box(0);
v_a_1003_ = lean_array_uget_borrowed(v_as_978_, v_i_980_);
if (lean_obj_tag(v_a_1003_) == 0)
{
v_a_996_ = v_snd_990_;
goto v___jp_995_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec(v_snd_990_);
v_val_1004_ = lean_ctor_get(v_a_1003_, 0);
v___x_1005_ = l_Lean_LocalDecl_type(v_val_1004_);
v___x_1006_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1005_, v_includeDelayed_977_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; 
lean_dec_ref(v___x_1006_);
v___x_1007_ = lean_box(0);
v___x_1008_ = 0;
v___x_1009_ = l_Lean_LocalDecl_value_x3f(v_val_1004_, v___x_1008_);
if (lean_obj_tag(v___x_1009_) == 1)
{
lean_object* v_val_1010_; lean_object* v___x_1011_; 
v_val_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_val_1010_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1010_, v_includeDelayed_977_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_dec_ref(v___x_1011_);
v_a_996_ = v___x_1007_;
goto v___jp_995_;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_del_object(v___x_992_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
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
else
{
lean_dec(v___x_1009_);
v_a_996_ = v___x_1007_;
goto v___jp_995_;
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_del_object(v___x_992_);
v_a_1020_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1006_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1006_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
v___jp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v_a_996_);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_a_996_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_980_, v___x_999_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_977_, v_as_978_, v_sz_979_, v___x_1000_, v___x_998_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_1001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(lean_object* v_init_1030_, uint8_t v_includeDelayed_1031_, lean_object* v_n_1032_, lean_object* v_b_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
if (lean_obj_tag(v_n_1032_) == 0)
{
lean_object* v_cs_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1074_; 
v_cs_1040_ = lean_ctor_get(v_n_1032_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_n_1032_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1042_ = v_n_1032_;
v_isShared_1043_ = v_isSharedCheck_1074_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_cs_1040_);
lean_dec(v_n_1032_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1074_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; size_t v_sz_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_b_1033_);
v_sz_1046_ = lean_array_size(v_cs_1040_);
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_1030_, v_includeDelayed_1031_, v_cs_1040_, v_sz_1046_, v___x_1047_, v___x_1045_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec_ref(v_cs_1040_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1065_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1065_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1065_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_fst_1053_; 
v_fst_1053_ = lean_ctor_get(v_a_1049_, 0);
if (lean_obj_tag(v_fst_1053_) == 0)
{
lean_object* v_snd_1054_; lean_object* v___x_1056_; 
v_snd_1054_ = lean_ctor_get(v_a_1049_, 1);
lean_inc(v_snd_1054_);
lean_dec(v_a_1049_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 1);
lean_ctor_set(v___x_1042_, 0, v_snd_1054_);
v___x_1056_ = v___x_1042_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_snd_1054_);
v___x_1056_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1056_);
v___x_1058_ = v___x_1051_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_val_1061_; lean_object* v___x_1063_; 
lean_inc_ref(v_fst_1053_);
lean_dec(v_a_1049_);
lean_del_object(v___x_1042_);
v_val_1061_ = lean_ctor_get(v_fst_1053_, 0);
lean_inc(v_val_1061_);
lean_dec_ref(v_fst_1053_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v_val_1061_);
v___x_1063_ = v___x_1051_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_val_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_del_object(v___x_1042_);
v_a_1066_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1048_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1048_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
else
{
lean_object* v_vs_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1109_; 
v_vs_1075_ = lean_ctor_get(v_n_1032_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_n_1032_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1077_ = v_n_1032_;
v_isShared_1078_ = v_isSharedCheck_1109_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_vs_1075_);
lean_dec(v_n_1032_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1109_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; size_t v_sz_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v_b_1033_);
v_sz_1081_ = lean_array_size(v_vs_1075_);
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_1031_, v_vs_1075_, v_sz_1081_, v___x_1082_, v___x_1080_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec_ref(v_vs_1075_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1100_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1100_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1100_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_fst_1088_; 
v_fst_1088_ = lean_ctor_get(v_a_1084_, 0);
if (lean_obj_tag(v_fst_1088_) == 0)
{
lean_object* v_snd_1089_; lean_object* v___x_1091_; 
v_snd_1089_ = lean_ctor_get(v_a_1084_, 1);
lean_inc(v_snd_1089_);
lean_dec(v_a_1084_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v_snd_1089_);
v___x_1091_ = v___x_1077_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_snd_1089_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1091_);
v___x_1093_ = v___x_1086_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_object* v_val_1096_; lean_object* v___x_1098_; 
lean_inc_ref(v_fst_1088_);
lean_dec(v_a_1084_);
lean_del_object(v___x_1077_);
v_val_1096_ = lean_ctor_get(v_fst_1088_, 0);
lean_inc(v_val_1096_);
lean_dec_ref(v_fst_1088_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v_val_1096_);
v___x_1098_ = v___x_1086_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_val_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_del_object(v___x_1077_);
v_a_1101_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1083_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1083_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(uint8_t v_includeDelayed_1110_, lean_object* v_as_1111_, size_t v_sz_1112_, size_t v_i_1113_, lean_object* v_b_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_usize_dec_lt(v_i_1113_, v_sz_1112_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_b_1114_);
return v___x_1122_;
}
else
{
lean_object* v_snd_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1161_; 
v_snd_1123_ = lean_ctor_get(v_b_1114_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_b_1114_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_b_1114_, 0);
lean_dec(v_unused_1162_);
v___x_1125_ = v_b_1114_;
v_isShared_1126_ = v_isSharedCheck_1161_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_snd_1123_);
lean_dec(v_b_1114_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1161_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v_a_1129_; lean_object* v_a_1136_; 
v___x_1127_ = lean_box(0);
v_a_1136_ = lean_array_uget_borrowed(v_as_1111_, v_i_1113_);
if (lean_obj_tag(v_a_1136_) == 0)
{
v_a_1129_ = v_snd_1123_;
goto v___jp_1128_;
}
else
{
lean_object* v_val_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_snd_1123_);
v_val_1137_ = lean_ctor_get(v_a_1136_, 0);
v___x_1138_ = l_Lean_LocalDecl_type(v_val_1137_);
v___x_1139_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1138_, v_includeDelayed_1110_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v___x_1139_);
v___x_1140_ = lean_box(0);
v___x_1141_ = 0;
v___x_1142_ = l_Lean_LocalDecl_value_x3f(v_val_1137_, v___x_1141_);
if (lean_obj_tag(v___x_1142_) == 1)
{
lean_object* v_val_1143_; lean_object* v___x_1144_; 
v_val_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_val_1143_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1143_, v_includeDelayed_1110_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_dec_ref(v___x_1144_);
v_a_1129_ = v___x_1140_;
goto v___jp_1128_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_1125_);
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
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
else
{
lean_dec(v___x_1142_);
v_a_1129_ = v___x_1140_;
goto v___jp_1128_;
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_del_object(v___x_1125_);
v_a_1153_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1139_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1139_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
v___jp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_a_1129_);
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1131_ = v___x_1125_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_a_1129_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
size_t v___x_1132_; size_t v___x_1133_; 
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = lean_usize_add(v_i_1113_, v___x_1132_);
v_i_1113_ = v___x_1133_;
v_b_1114_ = v___x_1131_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(uint8_t v_includeDelayed_1163_, lean_object* v_as_1164_, size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_usize_dec_lt(v_i_1166_, v_sz_1165_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v_b_1167_);
return v___x_1175_;
}
else
{
lean_object* v_snd_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1214_; 
v_snd_1176_ = lean_ctor_get(v_b_1167_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_b_1167_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v_b_1167_, 0);
lean_dec(v_unused_1215_);
v___x_1178_ = v_b_1167_;
v_isShared_1179_ = v_isSharedCheck_1214_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_snd_1176_);
lean_dec(v_b_1167_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1214_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v_a_1182_; lean_object* v_a_1189_; 
v___x_1180_ = lean_box(0);
v_a_1189_ = lean_array_uget_borrowed(v_as_1164_, v_i_1166_);
if (lean_obj_tag(v_a_1189_) == 0)
{
v_a_1182_ = v_snd_1176_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v_snd_1176_);
v_val_1190_ = lean_ctor_get(v_a_1189_, 0);
v___x_1191_ = l_Lean_LocalDecl_type(v_val_1190_);
v___x_1192_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1191_, v_includeDelayed_1163_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v___x_1192_);
v___x_1193_ = lean_box(0);
v___x_1194_ = 0;
v___x_1195_ = l_Lean_LocalDecl_value_x3f(v_val_1190_, v___x_1194_);
if (lean_obj_tag(v___x_1195_) == 1)
{
lean_object* v_val_1196_; lean_object* v___x_1197_; 
v_val_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_val_1196_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1196_, v_includeDelayed_1163_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_dec_ref(v___x_1197_);
v_a_1182_ = v___x_1193_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_del_object(v___x_1178_);
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_dec(v___x_1195_);
v_a_1182_ = v___x_1193_;
goto v___jp_1181_;
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_del_object(v___x_1178_);
v_a_1206_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1192_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1192_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
v___jp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v_a_1182_);
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1184_ = v___x_1178_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_a_1182_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
size_t v___x_1185_; size_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1166_, v___x_1185_);
v___x_1187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_1163_, v_as_1164_, v_sz_1165_, v___x_1186_, v___x_1184_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
return v___x_1187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(uint8_t v_includeDelayed_1216_, lean_object* v_t_1217_, lean_object* v_init_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_root_1225_; lean_object* v_tail_1226_; lean_object* v___x_1227_; 
v_root_1225_ = lean_ctor_get(v_t_1217_, 0);
lean_inc_ref(v_root_1225_);
v_tail_1226_ = lean_ctor_get(v_t_1217_, 1);
lean_inc_ref(v_tail_1226_);
lean_dec_ref(v_t_1217_);
v___x_1227_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1218_, v_includeDelayed_1216_, v_root_1225_, v_init_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1264_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1264_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1264_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
if (lean_obj_tag(v_a_1228_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; 
lean_dec_ref(v_tail_1226_);
v_a_1232_ = lean_ctor_get(v_a_1228_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v_a_1228_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_a_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; size_t v_sz_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
lean_del_object(v___x_1230_);
v_a_1236_ = lean_ctor_get(v_a_1228_, 0);
lean_inc(v_a_1236_);
lean_dec_ref(v_a_1228_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_a_1236_);
v_sz_1239_ = lean_array_size(v_tail_1226_);
v___x_1240_ = ((size_t)0ULL);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_1216_, v_tail_1226_, v_sz_1239_, v___x_1240_, v___x_1238_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec_ref(v_tail_1226_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1255_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1255_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1255_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_fst_1246_; 
v_fst_1246_ = lean_ctor_get(v_a_1242_, 0);
if (lean_obj_tag(v_fst_1246_) == 0)
{
lean_object* v_snd_1247_; lean_object* v___x_1249_; 
v_snd_1247_ = lean_ctor_get(v_a_1242_, 1);
lean_inc(v_snd_1247_);
lean_dec(v_a_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_snd_1247_);
v___x_1249_ = v___x_1244_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_snd_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
else
{
lean_object* v_val_1251_; lean_object* v___x_1253_; 
lean_inc_ref(v_fst_1246_);
lean_dec(v_a_1242_);
v_val_1251_ = lean_ctor_get(v_fst_1246_, 0);
lean_inc(v_val_1251_);
lean_dec_ref(v_fst_1246_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_val_1251_);
v___x_1253_ = v___x_1244_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_val_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1241_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1241_);
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
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v_tail_1226_);
v_a_1265_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1227_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1227_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object* v_mvarId_1273_, uint8_t v_includeDelayed_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v_fileName_1289_; lean_object* v_fileMap_1290_; lean_object* v_options_1291_; lean_object* v_currRecDepth_1292_; lean_object* v_maxRecDepth_1293_; lean_object* v_ref_1294_; lean_object* v_currNamespace_1295_; lean_object* v_openDecls_1296_; lean_object* v_initHeartbeats_1297_; lean_object* v_maxHeartbeats_1298_; lean_object* v_quotContext_1299_; lean_object* v_currMacroScope_1300_; uint8_t v_diag_1301_; lean_object* v_cancelTk_x3f_1302_; uint8_t v_suppressElabErrors_1303_; lean_object* v_inheritedTraceOptions_1304_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v_fileName_1289_ = lean_ctor_get(v_a_1278_, 0);
lean_inc_ref(v_fileName_1289_);
v_fileMap_1290_ = lean_ctor_get(v_a_1278_, 1);
lean_inc_ref(v_fileMap_1290_);
v_options_1291_ = lean_ctor_get(v_a_1278_, 2);
lean_inc_ref(v_options_1291_);
v_currRecDepth_1292_ = lean_ctor_get(v_a_1278_, 3);
lean_inc(v_currRecDepth_1292_);
v_maxRecDepth_1293_ = lean_ctor_get(v_a_1278_, 4);
lean_inc(v_maxRecDepth_1293_);
v_ref_1294_ = lean_ctor_get(v_a_1278_, 5);
lean_inc(v_ref_1294_);
v_currNamespace_1295_ = lean_ctor_get(v_a_1278_, 6);
lean_inc(v_currNamespace_1295_);
v_openDecls_1296_ = lean_ctor_get(v_a_1278_, 7);
lean_inc(v_openDecls_1296_);
v_initHeartbeats_1297_ = lean_ctor_get(v_a_1278_, 8);
lean_inc(v_initHeartbeats_1297_);
v_maxHeartbeats_1298_ = lean_ctor_get(v_a_1278_, 9);
lean_inc(v_maxHeartbeats_1298_);
v_quotContext_1299_ = lean_ctor_get(v_a_1278_, 10);
lean_inc(v_quotContext_1299_);
v_currMacroScope_1300_ = lean_ctor_get(v_a_1278_, 11);
lean_inc(v_currMacroScope_1300_);
v_diag_1301_ = lean_ctor_get_uint8(v_a_1278_, sizeof(void*)*14);
v_cancelTk_x3f_1302_ = lean_ctor_get(v_a_1278_, 12);
lean_inc(v_cancelTk_x3f_1302_);
v_suppressElabErrors_1303_ = lean_ctor_get_uint8(v_a_1278_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1304_ = lean_ctor_get(v_a_1278_, 13);
lean_inc_ref(v_inheritedTraceOptions_1304_);
lean_dec_ref(v_a_1278_);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_nat_dec_eq(v_maxRecDepth_1293_, v___x_1359_);
if (v___x_1360_ == 0)
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_nat_dec_eq(v_currRecDepth_1292_, v_maxRecDepth_1293_);
if (v___x_1361_ == 0)
{
goto v___jp_1305_;
}
else
{
lean_object* v___x_1362_; 
lean_dec_ref(v_inheritedTraceOptions_1304_);
lean_dec(v_cancelTk_x3f_1302_);
lean_dec(v_currMacroScope_1300_);
lean_dec(v_quotContext_1299_);
lean_dec(v_maxHeartbeats_1298_);
lean_dec(v_initHeartbeats_1297_);
lean_dec(v_openDecls_1296_);
lean_dec(v_currNamespace_1295_);
lean_dec(v_maxRecDepth_1293_);
lean_dec(v_currRecDepth_1292_);
lean_dec_ref(v_options_1291_);
lean_dec_ref(v_fileMap_1290_);
lean_dec_ref(v_fileName_1289_);
lean_dec(v_mvarId_1273_);
v___x_1362_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1294_);
return v___x_1362_;
}
}
else
{
goto v___jp_1305_;
}
v___jp_1281_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_st_ref_take(v_a_1275_);
lean_inc(v___y_1284_);
v___x_1286_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_1285_, v___y_1284_, v___y_1283_);
v___x_1287_ = lean_st_ref_set(v_a_1275_, v___x_1286_);
v_mvarId_1273_ = v___y_1284_;
v_a_1278_ = v___y_1282_;
goto _start;
}
v___jp_1305_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_add(v_currRecDepth_1292_, v___x_1306_);
lean_dec(v_currRecDepth_1292_);
v___x_1308_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1308_, 0, v_fileName_1289_);
lean_ctor_set(v___x_1308_, 1, v_fileMap_1290_);
lean_ctor_set(v___x_1308_, 2, v_options_1291_);
lean_ctor_set(v___x_1308_, 3, v___x_1307_);
lean_ctor_set(v___x_1308_, 4, v_maxRecDepth_1293_);
lean_ctor_set(v___x_1308_, 5, v_ref_1294_);
lean_ctor_set(v___x_1308_, 6, v_currNamespace_1295_);
lean_ctor_set(v___x_1308_, 7, v_openDecls_1296_);
lean_ctor_set(v___x_1308_, 8, v_initHeartbeats_1297_);
lean_ctor_set(v___x_1308_, 9, v_maxHeartbeats_1298_);
lean_ctor_set(v___x_1308_, 10, v_quotContext_1299_);
lean_ctor_set(v___x_1308_, 11, v_currMacroScope_1300_);
lean_ctor_set(v___x_1308_, 12, v_cancelTk_x3f_1302_);
lean_ctor_set(v___x_1308_, 13, v_inheritedTraceOptions_1304_);
lean_ctor_set_uint8(v___x_1308_, sizeof(void*)*14, v_diag_1301_);
lean_ctor_set_uint8(v___x_1308_, sizeof(void*)*14 + 1, v_suppressElabErrors_1303_);
lean_inc(v_mvarId_1273_);
v___x_1309_ = l_Lean_MVarId_getDecl(v_mvarId_1273_, v_a_1276_, v_a_1277_, v___x_1308_, v_a_1279_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v_lctx_1311_; lean_object* v_type_1312_; lean_object* v___x_1313_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1309_);
v_lctx_1311_ = lean_ctor_get(v_a_1310_, 1);
lean_inc_ref(v_lctx_1311_);
v_type_1312_ = lean_ctor_get(v_a_1310_, 2);
lean_inc_ref(v_type_1312_);
lean_dec(v_a_1310_);
v___x_1313_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_type_1312_, v_includeDelayed_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v___x_1308_, v_a_1279_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_decls_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref(v___x_1313_);
v_decls_1314_ = lean_ctor_get(v_lctx_1311_, 1);
lean_inc_ref(v_decls_1314_);
lean_dec_ref(v_lctx_1311_);
v___x_1315_ = lean_box(0);
v___x_1316_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_1274_, v_decls_1314_, v___x_1315_, v_a_1275_, v_a_1276_, v_a_1277_, v___x_1308_, v_a_1279_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref(v___x_1316_);
v___x_1317_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1273_, v_a_1277_);
lean_dec(v_mvarId_1273_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1342_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1342_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1342_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
if (lean_obj_tag(v_a_1318_) == 1)
{
lean_object* v_val_1322_; lean_object* v_mvarIdPending_1323_; lean_object* v___x_1324_; 
lean_del_object(v___x_1320_);
v_val_1322_ = lean_ctor_get(v_a_1318_, 0);
lean_inc(v_val_1322_);
lean_dec_ref(v_a_1318_);
v_mvarIdPending_1323_ = lean_ctor_get(v_val_1322_, 1);
lean_inc(v_mvarIdPending_1323_);
lean_dec(v_val_1322_);
v___x_1324_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarIdPending_1323_, v_a_1277_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; uint8_t v___x_1326_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1324_);
v___x_1326_ = lean_unbox(v_a_1325_);
lean_dec(v_a_1325_);
if (v___x_1326_ == 0)
{
v___y_1282_ = v___x_1308_;
v___y_1283_ = v___x_1315_;
v___y_1284_ = v_mvarIdPending_1323_;
goto v___jp_1281_;
}
else
{
v_mvarId_1273_ = v_mvarIdPending_1323_;
v_a_1278_ = v___x_1308_;
goto _start;
}
}
else
{
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1328_; uint8_t v___x_1329_; 
v_a_1328_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1324_);
v___x_1329_ = lean_unbox(v_a_1328_);
lean_dec(v_a_1328_);
if (v___x_1329_ == 0)
{
v_mvarId_1273_ = v_mvarIdPending_1323_;
v_a_1278_ = v___x_1308_;
goto _start;
}
else
{
v___y_1282_ = v___x_1308_;
v___y_1283_ = v___x_1315_;
v___y_1284_ = v_mvarIdPending_1323_;
goto v___jp_1281_;
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_mvarIdPending_1323_);
lean_dec_ref(v___x_1308_);
v_a_1331_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1324_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1324_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
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
}
else
{
lean_object* v___x_1340_; 
lean_dec(v_a_1318_);
lean_dec_ref(v___x_1308_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1315_);
v___x_1340_ = v___x_1320_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1315_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v___x_1308_);
v_a_1343_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1317_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1317_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_dec_ref(v___x_1308_);
lean_dec(v_mvarId_1273_);
return v___x_1316_;
}
}
else
{
lean_dec_ref(v_lctx_1311_);
lean_dec_ref(v___x_1308_);
lean_dec(v_mvarId_1273_);
return v___x_1313_;
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v___x_1308_);
lean_dec(v_mvarId_1273_);
v_a_1351_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1309_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1309_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(lean_object* v_as_1363_, size_t v_i_1364_, size_t v_stop_1365_, lean_object* v_b_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_usize_dec_eq(v_i_1364_, v_stop_1365_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_array_uget_borrowed(v_as_1363_, v_i_1364_);
lean_inc_ref(v___y_1370_);
lean_inc(v___x_1374_);
v___x_1375_ = l___private_Lean_Meta_CollectMVars_0__go(v___x_1374_, v___x_1373_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; size_t v___x_1377_; size_t v___x_1378_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_i_1364_, v___x_1377_);
v_i_1364_ = v___x_1378_;
v_b_1366_ = v_a_1376_;
goto _start;
}
else
{
return v___x_1375_;
}
}
else
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_b_1366_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object* v_as_1381_, lean_object* v_i_1382_, lean_object* v_stop_1383_, lean_object* v_b_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
size_t v_i_boxed_1391_; size_t v_stop_boxed_1392_; lean_object* v_res_1393_; 
v_i_boxed_1391_ = lean_unbox_usize(v_i_1382_);
lean_dec(v_i_1382_);
v_stop_boxed_1392_ = lean_unbox_usize(v_stop_1383_);
lean_dec(v_stop_1383_);
v_res_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_as_1381_, v_i_boxed_1391_, v_stop_boxed_1392_, v_b_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v_as_1381_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(lean_object* v_init_1394_, lean_object* v_includeDelayed_1395_, lean_object* v_as_1396_, lean_object* v_sz_1397_, lean_object* v_i_1398_, lean_object* v_b_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v_includeDelayed_boxed_1406_; size_t v_sz_boxed_1407_; size_t v_i_boxed_1408_; lean_object* v_res_1409_; 
v_includeDelayed_boxed_1406_ = lean_unbox(v_includeDelayed_1395_);
v_sz_boxed_1407_ = lean_unbox_usize(v_sz_1397_);
lean_dec(v_sz_1397_);
v_i_boxed_1408_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_1394_, v_includeDelayed_boxed_1406_, v_as_1396_, v_sz_boxed_1407_, v_i_boxed_1408_, v_b_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v_as_1396_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(lean_object* v_includeDelayed_1410_, lean_object* v_t_1411_, lean_object* v_init_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v_includeDelayed_boxed_1419_; lean_object* v_res_1420_; 
v_includeDelayed_boxed_1419_ = lean_unbox(v_includeDelayed_1410_);
v_res_1420_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_boxed_1419_, v_t_1411_, v_init_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object* v_includeDelayed_1421_, lean_object* v_as_1422_, lean_object* v_sz_1423_, lean_object* v_i_1424_, lean_object* v_b_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_includeDelayed_boxed_1432_; size_t v_sz_boxed_1433_; size_t v_i_boxed_1434_; lean_object* v_res_1435_; 
v_includeDelayed_boxed_1432_ = lean_unbox(v_includeDelayed_1421_);
v_sz_boxed_1433_ = lean_unbox_usize(v_sz_1423_);
lean_dec(v_sz_1423_);
v_i_boxed_1434_ = lean_unbox_usize(v_i_1424_);
lean_dec(v_i_1424_);
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_boxed_1432_, v_as_1422_, v_sz_boxed_1433_, v_i_boxed_1434_, v_b_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v_as_1422_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object* v_includeDelayed_1436_, lean_object* v_as_1437_, lean_object* v_sz_1438_, lean_object* v_i_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_includeDelayed_boxed_1447_; size_t v_sz_boxed_1448_; size_t v_i_boxed_1449_; lean_object* v_res_1450_; 
v_includeDelayed_boxed_1447_ = lean_unbox(v_includeDelayed_1436_);
v_sz_boxed_1448_ = lean_unbox_usize(v_sz_1438_);
lean_dec(v_sz_1438_);
v_i_boxed_1449_ = lean_unbox_usize(v_i_1439_);
lean_dec(v_i_1439_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_boxed_1447_, v_as_1437_, v_sz_boxed_1448_, v_i_boxed_1449_, v_b_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v_as_1437_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object* v_includeDelayed_1451_, lean_object* v_as_1452_, lean_object* v_sz_1453_, lean_object* v_i_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
uint8_t v_includeDelayed_boxed_1462_; size_t v_sz_boxed_1463_; size_t v_i_boxed_1464_; lean_object* v_res_1465_; 
v_includeDelayed_boxed_1462_ = lean_unbox(v_includeDelayed_1451_);
v_sz_boxed_1463_ = lean_unbox_usize(v_sz_1453_);
lean_dec(v_sz_1453_);
v_i_boxed_1464_ = lean_unbox_usize(v_i_1454_);
lean_dec(v_i_1454_);
v_res_1465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_boxed_1462_, v_as_1452_, v_sz_boxed_1463_, v_i_boxed_1464_, v_b_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v_as_1452_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object* v_includeDelayed_1466_, lean_object* v_as_1467_, lean_object* v_sz_1468_, lean_object* v_i_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v_includeDelayed_boxed_1477_; size_t v_sz_boxed_1478_; size_t v_i_boxed_1479_; lean_object* v_res_1480_; 
v_includeDelayed_boxed_1477_ = lean_unbox(v_includeDelayed_1466_);
v_sz_boxed_1478_ = lean_unbox_usize(v_sz_1468_);
lean_dec(v_sz_1468_);
v_i_boxed_1479_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_boxed_1477_, v_as_1467_, v_sz_boxed_1478_, v_i_boxed_1479_, v_b_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v_as_1467_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object* v_init_1481_, lean_object* v_includeDelayed_1482_, lean_object* v_n_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_includeDelayed_boxed_1491_; lean_object* v_res_1492_; 
v_includeDelayed_boxed_1491_ = lean_unbox(v_includeDelayed_1482_);
v_res_1492_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_1481_, v_includeDelayed_boxed_1491_, v_n_1483_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object* v_e_1493_, lean_object* v_includeDelayed_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
uint8_t v_includeDelayed_boxed_1501_; lean_object* v_res_1502_; 
v_includeDelayed_boxed_1501_ = lean_unbox(v_includeDelayed_1494_);
v_res_1502_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1493_, v_includeDelayed_boxed_1501_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go___boxed(lean_object* v_mvarId_1503_, lean_object* v_includeDelayed_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
uint8_t v_includeDelayed_boxed_1511_; lean_object* v_res_1512_; 
v_includeDelayed_boxed_1511_ = lean_unbox(v_includeDelayed_1504_);
v_res_1512_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1503_, v_includeDelayed_boxed_1511_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(lean_object* v_mvarId_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1513_, v___y_1516_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(lean_object* v_mvarId_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(v_mvarId_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec(v_mvarId_1521_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_object* v_00_u03b1_1529_, lean_object* v_ref_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1530_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(lean_object* v_00_u03b1_1538_, lean_object* v_ref_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(v_00_u03b1_1538_, v_ref_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(lean_object* v_00_u03b2_1547_, lean_object* v_m_1548_, lean_object* v_a_1549_, lean_object* v_b_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_1548_, v_a_1549_, v_b_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(lean_object* v_mvarId_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_1552_, v___y_1555_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(lean_object* v_mvarId_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_mvarId_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec(v_mvarId_1560_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(lean_object* v_mvarId_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_1568_, v___y_1571_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(lean_object* v_mvarId_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec(v_mvarId_1576_);
return v_res_1583_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_object* v_00_u03b2_1584_, lean_object* v_a_1585_, lean_object* v_x_1586_){
_start:
{
uint8_t v___x_1587_; 
v___x_1587_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_1585_, v_x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1588_, lean_object* v_a_1589_, lean_object* v_x_1590_){
_start:
{
uint8_t v_res_1591_; lean_object* v_r_1592_; 
v_res_1591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(v_00_u03b2_1588_, v_a_1589_, v_x_1590_);
lean_dec(v_x_1590_);
lean_dec(v_a_1589_);
v_r_1592_ = lean_box(v_res_1591_);
return v_r_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1(lean_object* v_00_u03b2_1593_, lean_object* v_data_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_data_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1596_, lean_object* v_i_1597_, lean_object* v_source_1598_, lean_object* v_target_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v_i_1597_, v_source_1598_, v_target_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_x_1602_, v_x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies(lean_object* v_mvarId_1605_, uint8_t v_includeDelayed_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1613_ = lean_st_mk_ref(v___x_1612_);
lean_inc_ref(v_a_1609_);
v___x_1614_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1605_, v_includeDelayed_1606_, v___x_1613_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1622_; 
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v___x_1614_, 0);
lean_dec(v_unused_1623_);
v___x_1616_ = v___x_1614_;
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
else
{
lean_dec(v___x_1614_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = lean_st_ref_get(v___x_1613_);
lean_dec(v___x_1613_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1618_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v___x_1613_);
v_a_1624_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1614_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1614_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object* v_mvarId_1632_, lean_object* v_includeDelayed_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
uint8_t v_includeDelayed_boxed_1639_; lean_object* v_res_1640_; 
v_includeDelayed_boxed_1639_ = lean_unbox(v_includeDelayed_1633_);
v_res_1640_ = l_Lean_MVarId_getMVarDependencies(v_mvarId_1632_, v_includeDelayed_boxed_1639_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies(lean_object* v_e_1641_, uint8_t v_includeDelayed_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1649_ = lean_st_mk_ref(v___x_1648_);
v___x_1650_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1641_, v_includeDelayed_1642_, v___x_1649_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v___x_1650_, 0);
lean_dec(v_unused_1659_);
v___x_1652_ = v___x_1650_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v___x_1650_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_st_ref_get(v___x_1649_);
lean_dec(v___x_1649_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v___x_1649_);
v_a_1660_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1650_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1650_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies___boxed(lean_object* v_e_1668_, lean_object* v_includeDelayed_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
uint8_t v_includeDelayed_boxed_1675_; lean_object* v_res_1676_; 
v_includeDelayed_boxed_1675_ = lean_unbox(v_includeDelayed_1669_);
v_res_1676_ = l_Lean_Expr_getMVarDependencies(v_e_1668_, v_includeDelayed_boxed_1675_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
return v_res_1676_;
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
