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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___lam__0(lean_object* v___x_73_, lean_object* v_00___74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_73_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___lam__0___boxed(lean_object* v___x_83_, lean_object* v_00___84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___lam__0(v___x_83_, v_00___84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(lean_object* v_a_92_, lean_object* v_b_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_array_100_; lean_object* v_start_101_; lean_object* v_stop_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_153_; 
v_array_100_ = lean_ctor_get(v_a_92_, 0);
v_start_101_ = lean_ctor_get(v_a_92_, 1);
v_stop_102_ = lean_ctor_get(v_a_92_, 2);
v_isSharedCheck_153_ = !lean_is_exclusive(v_a_92_);
if (v_isSharedCheck_153_ == 0)
{
v___x_104_ = v_a_92_;
v_isShared_105_ = v_isSharedCheck_153_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_stop_102_);
lean_inc(v_start_101_);
lean_inc(v_array_100_);
lean_dec(v_a_92_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_153_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint8_t v___x_106_; 
v___x_106_ = lean_nat_dec_lt(v_start_101_, v_stop_102_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_del_object(v___x_104_);
lean_dec(v_stop_102_);
lean_dec(v_start_101_);
lean_dec_ref(v_array_100_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v_b_93_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_array_fget_borrowed(v_array_100_, v_start_101_);
v___x_109_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v___x_108_, v___y_96_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref(v___x_109_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_add(v_start_101_, v___x_112_);
lean_dec(v_start_101_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_113_);
v___x_115_ = v___x_104_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_array_100_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_stop_102_);
v___x_115_ = v_reuseFailAlloc_144_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___y_117_; 
if (lean_obj_tag(v_a_110_) == 0)
{
lean_object* v___x_137_; 
v___x_137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___lam__0(v___x_111_, v___x_111_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
v___y_117_ = v___x_137_;
goto v___jp_116_;
}
else
{
lean_object* v_val_138_; lean_object* v_mvarIdPending_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_val_138_ = lean_ctor_get(v_a_110_, 0);
lean_inc(v_val_138_);
lean_dec_ref(v_a_110_);
v_mvarIdPending_139_ = lean_ctor_get(v_val_138_, 1);
lean_inc(v_mvarIdPending_139_);
lean_dec(v_val_138_);
v___x_140_ = l_Lean_mkMVar(v_mvarIdPending_139_);
v___x_141_ = l_Lean_Meta_collectMVars(v___x_140_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref(v___x_141_);
v___x_143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___lam__0(v___x_111_, v_a_142_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
v___y_117_ = v___x_143_;
goto v___jp_116_;
}
else
{
lean_dec_ref(v___x_115_);
return v___x_141_;
}
}
v___jp_116_:
{
if (lean_obj_tag(v___y_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_a_118_ = lean_ctor_get(v___y_117_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___y_117_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v___y_117_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___y_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
if (lean_obj_tag(v_a_118_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; 
lean_dec_ref(v___x_115_);
v_a_122_ = lean_ctor_get(v_a_118_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v_a_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v_a_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v_a_126_; 
lean_del_object(v___x_120_);
v_a_126_ = lean_ctor_get(v_a_118_, 0);
lean_inc(v_a_126_);
lean_dec_ref(v_a_118_);
v_a_92_ = v___x_115_;
v_b_93_ = v_a_126_;
goto _start;
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
lean_dec_ref(v___x_115_);
v_a_129_ = lean_ctor_get(v___y_117_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___y_117_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___y_117_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___y_117_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_del_object(v___x_104_);
lean_dec(v_stop_102_);
lean_dec(v_start_101_);
lean_dec_ref(v_array_100_);
v_a_145_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_109_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_109_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars(lean_object* v_e_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(v_e_154_, v_a_157_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v_result_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_result_167_; lean_object* v_lower_169_; lean_object* v_upper_170_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref(v___x_161_);
v___x_163_ = lean_st_ref_get(v_a_155_);
v_result_164_ = lean_ctor_get(v___x_163_, 1);
lean_inc_ref(v_result_164_);
v___x_165_ = l_Lean_Expr_collectMVars(v___x_163_, v_a_162_);
lean_inc_ref(v___x_165_);
v___x_166_ = lean_st_ref_set(v_a_155_, v___x_165_);
v_result_167_ = lean_ctor_get(v___x_165_, 1);
lean_inc_ref(v_result_167_);
lean_dec_ref(v___x_165_);
v___x_182_ = lean_array_get_size(v_result_164_);
lean_dec_ref(v_result_164_);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_array_get_size(v_result_167_);
v___x_185_ = lean_nat_dec_le(v___x_182_, v___x_183_);
if (v___x_185_ == 0)
{
v_lower_169_ = v___x_182_;
v_upper_170_ = v___x_184_;
goto v___jp_168_;
}
else
{
v_lower_169_ = v___x_183_;
v_upper_170_ = v___x_184_;
goto v___jp_168_;
}
v___jp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = l_Array_toSubarray___redArg(v_result_167_, v_lower_169_, v_upper_170_);
v___x_172_ = lean_box(0);
v___x_173_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v___x_171_, v___x_172_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v___x_173_, 0);
lean_dec(v_unused_181_);
v___x_175_ = v___x_173_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_dec(v___x_173_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_172_);
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_172_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
else
{
return v___x_173_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_a_186_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_161_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_161_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars___boxed(lean_object* v_e_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_collectMVars(v_e_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___boxed(lean_object* v_a_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_202_, v_b_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(lean_object* v_inst_211_, lean_object* v_R_212_, lean_object* v_a_213_, lean_object* v_b_214_, lean_object* v_c_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(v_a_213_, v_b_214_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___boxed(lean_object* v_inst_223_, lean_object* v_R_224_, lean_object* v_a_225_, lean_object* v_b_226_, lean_object* v_c_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(v_inst_223_, v_R_224_, v_a_225_, v_b_226_, v_c_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
return v_res_234_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__0(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_box(0);
v___x_236_ = lean_unsigned_to_nat(16u);
v___x_237_ = lean_mk_array(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__1(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__0, &l_Lean_Meta_getMVars___closed__0_once, _init_l_Lean_Meta_getMVars___closed__0);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__3(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_244_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__1, &l_Lean_Meta_getMVars___closed__1_once, _init_l_Lean_Meta_getMVars___closed__1);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars(lean_object* v_e_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_253_ = lean_st_mk_ref(v___x_252_);
v___x_254_ = l_Lean_Meta_collectMVars(v_e_246_, v___x_253_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_263_; 
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v___x_254_, 0);
lean_dec(v_unused_264_);
v___x_256_ = v___x_254_;
v_isShared_257_ = v_isSharedCheck_263_;
goto v_resetjp_255_;
}
else
{
lean_dec(v___x_254_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_263_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v_result_259_; lean_object* v___x_261_; 
v___x_258_ = lean_st_ref_get(v___x_253_);
lean_dec(v___x_253_);
v_result_259_ = lean_ctor_get(v___x_258_, 1);
lean_inc_ref(v_result_259_);
lean_dec(v___x_258_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v_result_259_);
v___x_261_ = v___x_256_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_result_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v___x_253_);
v_a_265_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_254_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_254_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars___boxed(lean_object* v_e_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_getMVars(v_e_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
return v_res_279_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_280_, lean_object* v_i_281_, lean_object* v_k_282_){
_start:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_array_get_size(v_keys_280_);
v___x_284_ = lean_nat_dec_lt(v_i_281_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec(v_i_281_);
return v___x_284_;
}
else
{
lean_object* v_k_x27_285_; uint8_t v___x_286_; 
v_k_x27_285_ = lean_array_fget_borrowed(v_keys_280_, v_i_281_);
v___x_286_ = l_Lean_instBEqMVarId_beq(v_k_282_, v_k_x27_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_i_281_, v___x_287_);
lean_dec(v_i_281_);
v_i_281_ = v___x_288_;
goto _start;
}
else
{
lean_dec(v_i_281_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_290_, lean_object* v_i_291_, lean_object* v_k_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_290_, v_i_291_, v_k_292_);
lean_dec(v_k_292_);
lean_dec_ref(v_keys_290_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; 
v___x_295_ = ((size_t)5ULL);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_shift_left(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; 
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_300_ = lean_usize_sub(v___x_299_, v___x_298_);
return v___x_300_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_301_, size_t v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_es_304_; lean_object* v___x_305_; size_t v___x_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v_j_309_; lean_object* v___x_310_; 
v_es_304_ = lean_ctor_get(v_x_301_, 0);
lean_inc_ref(v_es_304_);
lean_dec_ref(v_x_301_);
v___x_305_ = lean_box(2);
v___x_306_ = ((size_t)5ULL);
v___x_307_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_308_ = lean_usize_land(v_x_302_, v___x_307_);
v_j_309_ = lean_usize_to_nat(v___x_308_);
v___x_310_ = lean_array_get(v___x_305_, v_es_304_, v_j_309_);
lean_dec(v_j_309_);
lean_dec_ref(v_es_304_);
switch(lean_obj_tag(v___x_310_))
{
case 0:
{
lean_object* v_key_311_; uint8_t v___x_312_; 
v_key_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_key_311_);
lean_dec_ref(v___x_310_);
v___x_312_ = l_Lean_instBEqMVarId_beq(v_x_303_, v_key_311_);
lean_dec(v_key_311_);
return v___x_312_;
}
case 1:
{
lean_object* v_node_313_; size_t v___x_314_; 
v_node_313_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_node_313_);
lean_dec_ref(v___x_310_);
v___x_314_ = lean_usize_shift_right(v_x_302_, v___x_306_);
v_x_301_ = v_node_313_;
v_x_302_ = v___x_314_;
goto _start;
}
default: 
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
}
}
else
{
lean_object* v_ks_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_ks_317_ = lean_ctor_get(v_x_301_, 0);
lean_inc_ref(v_ks_317_);
lean_dec_ref(v_x_301_);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_317_, v___x_318_, v_x_303_);
lean_dec_ref(v_ks_317_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
size_t v_x_1555__boxed_323_; uint8_t v_res_324_; lean_object* v_r_325_; 
v_x_1555__boxed_323_ = lean_unbox_usize(v_x_321_);
lean_dec(v_x_321_);
v_res_324_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_320_, v_x_1555__boxed_323_, v_x_322_);
lean_dec(v_x_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
uint64_t v___x_328_; size_t v___x_329_; uint8_t v___x_330_; 
v___x_328_ = l_Lean_instHashableMVarId_hash(v_x_327_);
v___x_329_ = lean_uint64_to_usize(v___x_328_);
v___x_330_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_326_, v___x_329_, v_x_327_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg___boxed(lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_331_, v_x_332_);
lean_dec(v_x_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(lean_object* v_mvarId_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v_mctx_339_; lean_object* v_dAssignment_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_338_ = lean_st_ref_get(v___y_336_);
v_mctx_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc_ref(v_mctx_339_);
lean_dec(v___x_338_);
v_dAssignment_340_ = lean_ctor_get(v_mctx_339_, 8);
lean_inc_ref(v_dAssignment_340_);
lean_dec_ref(v_mctx_339_);
v___x_341_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_340_, v_mvarId_335_);
v___x_342_ = lean_box(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(lean_object* v_mvarId_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec(v_mvarId_344_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(lean_object* v_as_348_, size_t v_i_349_, size_t v_stop_350_, lean_object* v_b_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_a_358_; uint8_t v___x_362_; 
v___x_362_ = lean_usize_dec_eq(v_i_349_, v_stop_350_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_366_; 
v___x_363_ = lean_array_uget_borrowed(v_as_348_, v_i_349_);
v___x_366_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v___x_363_, v___y_353_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; uint8_t v___x_368_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_366_);
v___x_368_ = lean_unbox(v_a_367_);
lean_dec(v_a_367_);
if (v___x_368_ == 0)
{
goto v___jp_364_;
}
else
{
v_a_358_ = v_b_351_;
goto v___jp_357_;
}
}
else
{
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_369_; uint8_t v___x_370_; 
v_a_369_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_366_);
v___x_370_ = lean_unbox(v_a_369_);
lean_dec(v_a_369_);
if (v___x_370_ == 0)
{
v_a_358_ = v_b_351_;
goto v___jp_357_;
}
else
{
goto v___jp_364_;
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_b_351_);
v_a_371_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_366_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_366_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
v___jp_364_:
{
lean_object* v___x_365_; 
lean_inc(v___x_363_);
v___x_365_ = lean_array_push(v_b_351_, v___x_363_);
v_a_358_ = v___x_365_;
goto v___jp_357_;
}
}
else
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_b_351_);
return v___x_379_;
}
v___jp_357_:
{
size_t v___x_359_; size_t v___x_360_; 
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_add(v_i_349_, v___x_359_);
v_i_349_ = v___x_360_;
v_b_351_ = v_a_358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1___boxed(lean_object* v_as_380_, lean_object* v_i_381_, lean_object* v_stop_382_, lean_object* v_b_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
size_t v_i_boxed_389_; size_t v_stop_boxed_390_; lean_object* v_res_391_; 
v_i_boxed_389_ = lean_unbox_usize(v_i_381_);
lean_dec(v_i_381_);
v_stop_boxed_390_ = lean_unbox_usize(v_stop_382_);
lean_dec(v_stop_382_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_380_, v_i_boxed_389_, v_stop_boxed_390_, v_b_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v_as_380_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_getMVars(v_e_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_420_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_420_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_420_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_420_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_array_get_size(v_a_399_);
v___x_405_ = ((lean_object*)(l_Lean_Meta_getMVars___closed__2));
v___x_406_ = lean_nat_dec_lt(v___x_403_, v___x_404_);
if (v___x_406_ == 0)
{
lean_object* v___x_408_; 
lean_dec(v_a_399_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_405_);
v___x_408_ = v___x_401_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_405_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
else
{
uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_le(v___x_404_, v___x_404_);
if (v___x_410_ == 0)
{
if (v___x_406_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v_a_399_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_405_);
v___x_412_ = v___x_401_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_405_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
else
{
size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
lean_del_object(v___x_401_);
v___x_414_ = ((size_t)0ULL);
v___x_415_ = lean_usize_of_nat(v___x_404_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_399_, v___x_414_, v___x_415_, v___x_405_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_399_);
return v___x_416_;
}
}
else
{
size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
lean_del_object(v___x_401_);
v___x_417_ = ((size_t)0ULL);
v___x_418_ = lean_usize_of_nat(v___x_404_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_399_, v___x_417_, v___x_418_, v___x_405_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_399_);
return v___x_419_;
}
}
}
}
else
{
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object* v_e_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_getMVarsNoDelayed(v_e_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(lean_object* v_mvarId_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v_mvarId_428_, v___y_430_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(lean_object* v_mvarId_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(v_mvarId_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v_mvarId_435_);
return v_res_441_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(lean_object* v_00_u03b2_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_443_, v_x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(v_00_u03b2_446_, v_x_447_, v_x_448_);
lean_dec(v_x_448_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_451_, lean_object* v_x_452_, size_t v_x_453_, lean_object* v_x_454_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_452_, v_x_453_, v_x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
size_t v_x_1778__boxed_460_; uint8_t v_res_461_; lean_object* v_r_462_; 
v_x_1778__boxed_460_ = lean_unbox_usize(v_x_458_);
lean_dec(v_x_458_);
v_res_461_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(v_00_u03b2_456_, v_x_457_, v_x_1778__boxed_460_, v_x_459_);
lean_dec(v_x_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_463_, lean_object* v_keys_464_, lean_object* v_vals_465_, lean_object* v_heq_466_, lean_object* v_i_467_, lean_object* v_k_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_464_, v_i_467_, v_k_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_470_, lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_heq_473_, lean_object* v_i_474_, lean_object* v_k_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_470_, v_keys_471_, v_vals_472_, v_heq_473_, v_i_474_, v_k_475_);
lean_dec(v_k_475_);
lean_dec_ref(v_vals_472_);
lean_dec_ref(v_keys_471_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_x_478_);
return v___x_486_;
}
else
{
lean_object* v_head_487_; lean_object* v_tail_488_; lean_object* v_type_489_; lean_object* v___x_490_; 
v_head_487_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_head_487_);
v_tail_488_ = lean_ctor_get(v_x_479_, 1);
lean_inc(v_tail_488_);
lean_dec_ref(v_x_479_);
v_type_489_ = lean_ctor_get(v_head_487_, 1);
lean_inc_ref(v_type_489_);
lean_dec(v_head_487_);
v___x_490_ = l_Lean_Meta_collectMVars(v_type_489_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v_x_478_ = v_a_491_;
v_x_479_ = v_tail_488_;
goto _start;
}
else
{
lean_dec(v_tail_488_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_493_, v_x_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v_x_502_);
return v___x_510_;
}
else
{
lean_object* v_head_511_; lean_object* v_tail_512_; lean_object* v___y_514_; lean_object* v_type_517_; lean_object* v_ctors_518_; lean_object* v___x_519_; 
v_head_511_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_head_511_);
v_tail_512_ = lean_ctor_get(v_x_503_, 1);
lean_inc(v_tail_512_);
lean_dec_ref(v_x_503_);
v_type_517_ = lean_ctor_get(v_head_511_, 1);
lean_inc_ref(v_type_517_);
v_ctors_518_ = lean_ctor_get(v_head_511_, 2);
lean_inc(v_ctors_518_);
lean_dec(v_head_511_);
v___x_519_ = l_Lean_Meta_collectMVars(v_type_517_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v___x_519_);
v___x_521_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_a_520_, v_ctors_518_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
v___y_514_ = v___x_521_;
goto v___jp_513_;
}
else
{
lean_dec(v_ctors_518_);
v___y_514_ = v___x_519_;
goto v___jp_513_;
}
v___jp_513_:
{
if (lean_obj_tag(v___y_514_) == 0)
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___y_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___y_514_);
v_x_502_ = v_a_515_;
v_x_503_ = v_tail_512_;
goto _start;
}
else
{
lean_dec(v_tail_512_);
return v___y_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_522_, v_x_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v_x_531_);
return v___x_539_;
}
else
{
lean_object* v_head_540_; lean_object* v_tail_541_; lean_object* v___y_543_; lean_object* v_toConstantVal_546_; lean_object* v_value_547_; lean_object* v_type_548_; lean_object* v___x_549_; 
v_head_540_ = lean_ctor_get(v_x_532_, 0);
lean_inc(v_head_540_);
v_tail_541_ = lean_ctor_get(v_x_532_, 1);
lean_inc(v_tail_541_);
lean_dec_ref(v_x_532_);
v_toConstantVal_546_ = lean_ctor_get(v_head_540_, 0);
lean_inc_ref(v_toConstantVal_546_);
v_value_547_ = lean_ctor_get(v_head_540_, 1);
lean_inc_ref(v_value_547_);
lean_dec(v_head_540_);
v_type_548_ = lean_ctor_get(v_toConstantVal_546_, 2);
lean_inc_ref(v_type_548_);
lean_dec_ref(v_toConstantVal_546_);
v___x_549_ = l_Lean_Meta_collectMVars(v_type_548_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; 
lean_dec_ref(v___x_549_);
v___x_550_ = l_Lean_Meta_collectMVars(v_value_547_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
v___y_543_ = v___x_550_;
goto v___jp_542_;
}
else
{
lean_dec_ref(v_value_547_);
v___y_543_ = v___x_549_;
goto v___jp_542_;
}
v___jp_542_:
{
if (lean_obj_tag(v___y_543_) == 0)
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v___y_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v___y_543_);
v_x_531_ = v_a_544_;
v_x_532_ = v_tail_541_;
goto _start;
}
else
{
lean_dec(v_tail_541_);
return v___y_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_551_, v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(lean_object* v_d_560_, lean_object* v_a_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
switch(lean_obj_tag(v_d_560_))
{
case 0:
{
lean_object* v_val_568_; lean_object* v_toConstantVal_569_; lean_object* v_type_570_; lean_object* v___x_571_; 
v_val_568_ = lean_ctor_get(v_d_560_, 0);
lean_inc_ref(v_val_568_);
lean_dec_ref(v_d_560_);
v_toConstantVal_569_ = lean_ctor_get(v_val_568_, 0);
lean_inc_ref(v_toConstantVal_569_);
lean_dec_ref(v_val_568_);
v_type_570_ = lean_ctor_get(v_toConstantVal_569_, 2);
lean_inc_ref(v_type_570_);
lean_dec_ref(v_toConstantVal_569_);
v___x_571_ = l_Lean_Meta_collectMVars(v_type_570_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_571_;
}
case 4:
{
lean_object* v___x_572_; 
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v_a_561_);
return v___x_572_;
}
case 5:
{
lean_object* v_defns_573_; lean_object* v___x_574_; 
v_defns_573_ = lean_ctor_get(v_d_560_, 0);
lean_inc(v_defns_573_);
lean_dec_ref(v_d_560_);
v___x_574_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_a_561_, v_defns_573_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_574_;
}
case 6:
{
lean_object* v_types_575_; lean_object* v___x_576_; 
v_types_575_ = lean_ctor_get(v_d_560_, 2);
lean_inc(v_types_575_);
lean_dec_ref(v_d_560_);
v___x_576_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_a_561_, v_types_575_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_576_;
}
default: 
{
lean_object* v_val_577_; lean_object* v_toConstantVal_578_; lean_object* v_value_579_; lean_object* v_type_580_; lean_object* v___x_581_; 
v_val_577_ = lean_ctor_get(v_d_560_, 0);
lean_inc_ref(v_val_577_);
lean_dec(v_d_560_);
v_toConstantVal_578_ = lean_ctor_get(v_val_577_, 0);
lean_inc_ref(v_toConstantVal_578_);
v_value_579_ = lean_ctor_get(v_val_577_, 1);
lean_inc_ref(v_value_579_);
lean_dec_ref(v_val_577_);
v_type_580_ = lean_ctor_get(v_toConstantVal_578_, 2);
lean_inc_ref(v_type_580_);
lean_dec_ref(v_toConstantVal_578_);
v___x_581_ = l_Lean_Meta_collectMVars(v_type_580_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v___x_581_);
v___x_582_ = l_Lean_Meta_collectMVars(v_value_579_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_582_;
}
else
{
lean_dec_ref(v_value_579_);
return v___x_581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(lean_object* v_d_583_, lean_object* v_a_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_583_, v_a_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object* v_d_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_box(0);
v___x_600_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(v_d_592_, v___x_599_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object* v_d_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Meta_collectMVarsAtDecl(v_d_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object* v_d_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_Lean_Meta_getMVars___closed__3, &l_Lean_Meta_getMVars___closed__3_once, _init_l_Lean_Meta_getMVars___closed__3);
v___x_616_ = lean_st_mk_ref(v___x_615_);
v___x_617_ = l_Lean_Meta_collectMVarsAtDecl(v_d_609_, v___x_616_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_626_; 
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_627_);
v___x_619_ = v___x_617_;
v_isShared_620_ = v_isSharedCheck_626_;
goto v_resetjp_618_;
}
else
{
lean_dec(v___x_617_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_626_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v_result_622_; lean_object* v___x_624_; 
v___x_621_ = lean_st_ref_get(v___x_616_);
lean_dec(v___x_616_);
v_result_622_ = lean_ctor_get(v___x_621_, 1);
lean_inc_ref(v_result_622_);
lean_dec(v___x_621_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_result_622_);
v___x_624_ = v___x_619_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_result_622_);
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
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v___x_616_);
v_a_628_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_617_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_617_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object* v_d_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_getMVarsAtDecl(v_d_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(lean_object* v_mvarId_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; lean_object* v_mctx_647_; lean_object* v_dAssignment_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = lean_st_ref_get(v___y_644_);
v_mctx_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc_ref(v_mctx_647_);
lean_dec(v___x_646_);
v_dAssignment_648_ = lean_ctor_get(v_mctx_647_, 8);
lean_inc_ref(v_dAssignment_648_);
lean_dec_ref(v_mctx_647_);
v___x_649_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_648_, v_mvarId_643_);
v___x_650_ = lean_box(v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(lean_object* v_mvarId_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec(v_mvarId_652_);
return v_res_655_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(lean_object* v_a_656_, lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
else
{
lean_object* v_key_659_; lean_object* v_tail_660_; uint8_t v___x_661_; 
v_key_659_ = lean_ctor_get(v_x_657_, 0);
v_tail_660_ = lean_ctor_get(v_x_657_, 2);
v___x_661_ = l_Lean_instBEqMVarId_beq(v_key_659_, v_a_656_);
if (v___x_661_ == 0)
{
v_x_657_ = v_tail_660_;
goto _start;
}
else
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_663_, lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_663_, v_x_664_);
lean_dec(v_x_664_);
lean_dec(v_a_663_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
return v_x_667_;
}
else
{
lean_object* v_key_669_; lean_object* v_value_670_; lean_object* v_tail_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_694_; 
v_key_669_ = lean_ctor_get(v_x_668_, 0);
v_value_670_ = lean_ctor_get(v_x_668_, 1);
v_tail_671_ = lean_ctor_get(v_x_668_, 2);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_668_);
if (v_isSharedCheck_694_ == 0)
{
v___x_673_ = v_x_668_;
v_isShared_674_ = v_isSharedCheck_694_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_tail_671_);
lean_inc(v_value_670_);
lean_inc(v_key_669_);
lean_dec(v_x_668_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_694_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; uint64_t v___x_676_; uint64_t v___x_677_; uint64_t v___x_678_; uint64_t v_fold_679_; uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_675_ = lean_array_get_size(v_x_667_);
v___x_676_ = l_Lean_instHashableMVarId_hash(v_key_669_);
v___x_677_ = 32ULL;
v___x_678_ = lean_uint64_shift_right(v___x_676_, v___x_677_);
v_fold_679_ = lean_uint64_xor(v___x_676_, v___x_678_);
v___x_680_ = 16ULL;
v___x_681_ = lean_uint64_shift_right(v_fold_679_, v___x_680_);
v___x_682_ = lean_uint64_xor(v_fold_679_, v___x_681_);
v___x_683_ = lean_uint64_to_usize(v___x_682_);
v___x_684_ = lean_usize_of_nat(v___x_675_);
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_sub(v___x_684_, v___x_685_);
v___x_687_ = lean_usize_land(v___x_683_, v___x_686_);
v___x_688_ = lean_array_uget_borrowed(v_x_667_, v___x_687_);
lean_inc(v___x_688_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 2, v___x_688_);
v___x_690_ = v___x_673_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_key_669_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_value_670_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v___x_688_);
v___x_690_ = v_reuseFailAlloc_693_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; 
v___x_691_ = lean_array_uset(v_x_667_, v___x_687_, v___x_690_);
v_x_667_ = v___x_691_;
v_x_668_ = v_tail_671_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(lean_object* v_i_695_, lean_object* v_source_696_, lean_object* v_target_697_){
_start:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_array_get_size(v_source_696_);
v___x_699_ = lean_nat_dec_lt(v_i_695_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec_ref(v_source_696_);
lean_dec(v_i_695_);
return v_target_697_;
}
else
{
lean_object* v_es_700_; lean_object* v___x_701_; lean_object* v_source_702_; lean_object* v_target_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_es_700_ = lean_array_fget(v_source_696_, v_i_695_);
v___x_701_ = lean_box(0);
v_source_702_ = lean_array_fset(v_source_696_, v_i_695_, v___x_701_);
v_target_703_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_target_697_, v_es_700_);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_i_695_, v___x_704_);
lean_dec(v_i_695_);
v_i_695_ = v___x_705_;
v_source_696_ = v_source_702_;
v_target_697_ = v_target_703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(lean_object* v_data_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_nbuckets_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_708_ = lean_array_get_size(v_data_707_);
v___x_709_ = lean_unsigned_to_nat(2u);
v_nbuckets_710_ = lean_nat_mul(v___x_708_, v___x_709_);
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_box(0);
v___x_713_ = lean_mk_array(v_nbuckets_710_, v___x_712_);
v___x_714_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v___x_711_, v_data_707_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(lean_object* v_m_715_, lean_object* v_a_716_, lean_object* v_b_717_){
_start:
{
lean_object* v_size_718_; lean_object* v_buckets_719_; lean_object* v___x_720_; uint64_t v___x_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v_fold_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; lean_object* v_bkt_733_; uint8_t v___x_734_; 
v_size_718_ = lean_ctor_get(v_m_715_, 0);
v_buckets_719_ = lean_ctor_get(v_m_715_, 1);
v___x_720_ = lean_array_get_size(v_buckets_719_);
v___x_721_ = l_Lean_instHashableMVarId_hash(v_a_716_);
v___x_722_ = 32ULL;
v___x_723_ = lean_uint64_shift_right(v___x_721_, v___x_722_);
v_fold_724_ = lean_uint64_xor(v___x_721_, v___x_723_);
v___x_725_ = 16ULL;
v___x_726_ = lean_uint64_shift_right(v_fold_724_, v___x_725_);
v___x_727_ = lean_uint64_xor(v_fold_724_, v___x_726_);
v___x_728_ = lean_uint64_to_usize(v___x_727_);
v___x_729_ = lean_usize_of_nat(v___x_720_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_sub(v___x_729_, v___x_730_);
v___x_732_ = lean_usize_land(v___x_728_, v___x_731_);
v_bkt_733_ = lean_array_uget_borrowed(v_buckets_719_, v___x_732_);
v___x_734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_716_, v_bkt_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_755_; 
lean_inc_ref(v_buckets_719_);
lean_inc(v_size_718_);
v_isSharedCheck_755_ = !lean_is_exclusive(v_m_715_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; lean_object* v_unused_757_; 
v_unused_756_ = lean_ctor_get(v_m_715_, 1);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_m_715_, 0);
lean_dec(v_unused_757_);
v___x_736_ = v_m_715_;
v_isShared_737_ = v_isSharedCheck_755_;
goto v_resetjp_735_;
}
else
{
lean_dec(v_m_715_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_755_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v_size_x27_739_; lean_object* v___x_740_; lean_object* v_buckets_x27_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_738_ = lean_unsigned_to_nat(1u);
v_size_x27_739_ = lean_nat_add(v_size_718_, v___x_738_);
lean_dec(v_size_718_);
lean_inc(v_bkt_733_);
v___x_740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_740_, 0, v_a_716_);
lean_ctor_set(v___x_740_, 1, v_b_717_);
lean_ctor_set(v___x_740_, 2, v_bkt_733_);
v_buckets_x27_741_ = lean_array_uset(v_buckets_719_, v___x_732_, v___x_740_);
v___x_742_ = lean_unsigned_to_nat(4u);
v___x_743_ = lean_nat_mul(v_size_x27_739_, v___x_742_);
v___x_744_ = lean_unsigned_to_nat(3u);
v___x_745_ = lean_nat_div(v___x_743_, v___x_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_array_get_size(v_buckets_x27_741_);
v___x_747_ = lean_nat_dec_le(v___x_745_, v___x_746_);
lean_dec(v___x_745_);
if (v___x_747_ == 0)
{
lean_object* v_val_748_; lean_object* v___x_750_; 
v_val_748_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_buckets_x27_741_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_val_748_);
lean_ctor_set(v___x_736_, 0, v_size_x27_739_);
v___x_750_ = v___x_736_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_size_x27_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_val_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v___x_753_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_buckets_x27_741_);
lean_ctor_set(v___x_736_, 0, v_size_x27_739_);
v___x_753_ = v___x_736_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_size_x27_739_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_buckets_x27_741_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_dec(v_b_717_);
lean_dec(v_a_716_);
return v_m_715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(uint8_t v_includeDelayed_758_, lean_object* v_as_759_, size_t v_sz_760_, size_t v_i_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_a_770_; uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_lt(v_i_761_, v_sz_760_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_b_762_);
return v___x_775_;
}
else
{
lean_object* v_a_776_; 
v_a_776_ = lean_array_uget_borrowed(v_as_759_, v_i_761_);
if (v_includeDelayed_758_ == 0)
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_a_776_, v___y_765_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; uint8_t v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
v___x_782_ = lean_unbox(v_a_781_);
lean_dec(v_a_781_);
if (v___x_782_ == 0)
{
goto v___jp_777_;
}
else
{
v_a_770_ = v_b_762_;
goto v___jp_769_;
}
}
else
{
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_783_; uint8_t v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_780_);
v___x_784_ = lean_unbox(v_a_783_);
lean_dec(v_a_783_);
if (v___x_784_ == 0)
{
v_a_770_ = v_b_762_;
goto v___jp_769_;
}
else
{
goto v___jp_777_;
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v_b_762_);
v_a_785_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_780_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_780_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
else
{
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_box(0);
lean_inc(v_a_776_);
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_b_762_, v_a_776_, v___x_778_);
v_a_770_ = v___x_779_;
goto v___jp_769_;
}
}
v___jp_769_:
{
size_t v___x_771_; size_t v___x_772_; 
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_761_, v___x_771_);
v_i_761_ = v___x_772_;
v_b_762_ = v_a_770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___boxed(lean_object* v_includeDelayed_793_, lean_object* v_as_794_, lean_object* v_sz_795_, lean_object* v_i_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
uint8_t v_includeDelayed_boxed_804_; size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_includeDelayed_boxed_804_ = lean_unbox(v_includeDelayed_793_);
v_sz_boxed_805_ = lean_unbox_usize(v_sz_795_);
lean_dec(v_sz_795_);
v_i_boxed_806_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_boxed_804_, v_as_794_, v_sz_boxed_805_, v_i_boxed_806_, v_b_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v_as_794_);
return v_res_807_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = l_Lean_maxRecDepthErrorMessage;
v___x_814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3);
v___x_816_ = l_Lean_MessageData_ofFormat(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4);
v___x_818_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2));
v___x_819_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v___x_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(lean_object* v_ref_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_ref_820_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(lean_object* v_ref_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(lean_object* v_mvarId_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_mctx_832_; lean_object* v_eAssignment_833_; lean_object* v_dAssignment_834_; uint8_t v___x_835_; 
v___x_831_ = lean_st_ref_get(v___y_829_);
v_mctx_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_mctx_832_);
lean_dec(v___x_831_);
v_eAssignment_833_ = lean_ctor_get(v_mctx_832_, 7);
lean_inc_ref(v_eAssignment_833_);
v_dAssignment_834_ = lean_ctor_get(v_mctx_832_, 8);
lean_inc_ref(v_dAssignment_834_);
lean_dec_ref(v_mctx_832_);
v___x_835_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_eAssignment_833_, v_mvarId_828_);
if (v___x_835_ == 0)
{
uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_834_, v_mvarId_828_);
v___x_837_ = lean_box(v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_dAssignment_834_);
v___x_839_ = lean_box(v___x_835_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(lean_object* v_mvarId_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec(v_mvarId_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(lean_object* v_mvarId_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; lean_object* v_mctx_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_st_ref_get(v___y_846_);
v_mctx_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc_ref(v_mctx_849_);
lean_dec(v___x_848_);
v___x_850_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_849_, v_mvarId_845_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg___boxed(lean_object* v_mvarId_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec(v_mvarId_852_);
return v_res_855_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_box(0);
v___x_857_ = lean_unsigned_to_nat(16u);
v___x_858_ = lean_mk_array(v___x_857_, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars(lean_object* v_e_862_, uint8_t v_includeDelayed_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_getMVars(v_e_862_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; size_t v_sz_876_; size_t v___x_877_; lean_object* v___x_878_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v___x_870_);
v___x_872_ = lean_st_ref_get(v_a_864_);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_875_ = lean_st_ref_set(v_a_864_, v___x_874_);
v_sz_876_ = lean_array_size(v_a_871_);
v___x_877_ = ((size_t)0ULL);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_863_, v_a_871_, v_sz_876_, v___x_877_, v___x_872_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_898_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_898_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_898_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_898_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_883_ = lean_st_ref_set(v_a_864_, v_a_879_);
v___x_884_ = lean_array_get_size(v_a_871_);
v___x_885_ = lean_box(0);
v___x_886_ = lean_nat_dec_lt(v___x_873_, v___x_884_);
if (v___x_886_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v_a_871_);
lean_dec_ref(v_a_867_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_885_);
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_885_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
uint8_t v___x_890_; 
v___x_890_ = lean_nat_dec_le(v___x_884_, v___x_884_);
if (v___x_890_ == 0)
{
if (v___x_886_ == 0)
{
lean_object* v___x_892_; 
lean_dec(v_a_871_);
lean_dec_ref(v_a_867_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_885_);
v___x_892_ = v___x_881_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_885_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
size_t v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_881_);
v___x_894_ = lean_usize_of_nat(v___x_884_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_871_, v___x_877_, v___x_894_, v___x_885_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_a_871_);
return v___x_895_;
}
}
else
{
size_t v___x_896_; lean_object* v___x_897_; 
lean_del_object(v___x_881_);
v___x_896_ = lean_usize_of_nat(v___x_884_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_871_, v___x_877_, v___x_896_, v___x_885_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_a_871_);
return v___x_897_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec(v_a_871_);
lean_dec_ref(v_a_867_);
v_a_899_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_878_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_878_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v_a_867_);
v_a_907_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_870_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_870_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(uint8_t v_includeDelayed_915_, lean_object* v___x_916_, lean_object* v___x_917_, lean_object* v_inh_918_, lean_object* v_as_919_, size_t v_sz_920_, size_t v_i_921_, lean_object* v_b_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = lean_usize_dec_lt(v_i_921_, v_sz_920_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v___y_926_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v_b_922_);
return v___x_930_;
}
else
{
lean_object* v_snd_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_965_; 
v_snd_931_ = lean_ctor_get(v_b_922_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_b_922_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_b_922_, 0);
lean_dec(v_unused_966_);
v___x_933_ = v_b_922_;
v_isShared_934_ = v_isSharedCheck_965_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snd_931_);
lean_dec(v_b_922_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_965_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_a_935_; lean_object* v___x_936_; 
v_a_935_ = lean_array_uget_borrowed(v_as_919_, v_i_921_);
lean_inc_ref(v___y_926_);
lean_inc(v_snd_931_);
lean_inc(v_a_935_);
v___x_936_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_includeDelayed_915_, v___x_916_, v___x_917_, v_inh_918_, v_a_935_, v_snd_931_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_956_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_956_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_956_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_956_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
if (lean_obj_tag(v_a_937_) == 0)
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec_ref(v___y_926_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_a_937_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_941_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_931_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_943_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
lean_del_object(v___x_939_);
lean_dec(v_snd_931_);
v_a_948_ = lean_ctor_get(v_a_937_, 0);
lean_inc(v_a_948_);
lean_dec_ref(v_a_937_);
v___x_949_ = lean_box(0);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_a_948_);
lean_ctor_set(v___x_933_, 0, v___x_949_);
v___x_951_ = v___x_933_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_a_948_);
v___x_951_ = v_reuseFailAlloc_955_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
size_t v___x_952_; size_t v___x_953_; 
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_add(v_i_921_, v___x_952_);
v_i_921_ = v___x_953_;
v_b_922_ = v___x_951_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_del_object(v___x_933_);
lean_dec(v_snd_931_);
lean_dec_ref(v___y_926_);
v_a_957_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_936_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_936_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(uint8_t v_includeDelayed_967_, lean_object* v___x_968_, lean_object* v___x_969_, lean_object* v_as_970_, size_t v_sz_971_, size_t v_i_972_, lean_object* v_b_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
uint8_t v___x_980_; 
v___x_980_ = lean_usize_dec_lt(v_i_972_, v_sz_971_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec_ref(v___y_977_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_b_973_);
return v___x_981_;
}
else
{
lean_object* v_snd_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1020_; 
v_snd_982_ = lean_ctor_get(v_b_973_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_b_973_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_b_973_, 0);
lean_dec(v_unused_1021_);
v___x_984_ = v_b_973_;
v_isShared_985_ = v_isSharedCheck_1020_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snd_982_);
lean_dec(v_b_973_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1020_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v_a_988_; lean_object* v_a_995_; 
v___x_986_ = lean_box(0);
v_a_995_ = lean_array_uget_borrowed(v_as_970_, v_i_972_);
if (lean_obj_tag(v_a_995_) == 0)
{
v_a_988_ = v_snd_982_;
goto v___jp_987_;
}
else
{
lean_object* v_val_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec(v_snd_982_);
v_val_996_ = lean_ctor_get(v_a_995_, 0);
v___x_997_ = l_Lean_LocalDecl_type(v_val_996_);
lean_inc_ref(v___y_977_);
v___x_998_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_997_, v_includeDelayed_967_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_998_) == 0)
{
uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec_ref(v___x_998_);
v___x_999_ = lean_nat_dec_eq(v___x_968_, v___x_969_);
v___x_1000_ = lean_box(0);
v___x_1001_ = l_Lean_LocalDecl_value_x3f(v_val_996_, v___x_999_);
if (lean_obj_tag(v___x_1001_) == 1)
{
lean_object* v_val_1002_; lean_object* v___x_1003_; 
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref(v___x_1001_);
lean_inc_ref(v___y_977_);
v___x_1003_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1002_, v_includeDelayed_967_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_dec_ref(v___x_1003_);
v_a_988_ = v___x_1000_;
goto v___jp_987_;
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_del_object(v___x_984_);
lean_dec_ref(v___y_977_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_dec(v___x_1001_);
v_a_988_ = v___x_1000_;
goto v___jp_987_;
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_del_object(v___x_984_);
lean_dec_ref(v___y_977_);
v_a_1012_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_998_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_998_);
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
v___jp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v_a_988_);
lean_ctor_set(v___x_984_, 0, v___x_986_);
v___x_990_ = v___x_984_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_a_988_);
v___x_990_ = v_reuseFailAlloc_994_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
size_t v___x_991_; size_t v___x_992_; 
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_add(v_i_972_, v___x_991_);
v_i_972_ = v___x_992_;
v_b_973_ = v___x_990_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(uint8_t v_includeDelayed_1022_, lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v_as_1025_, size_t v_sz_1026_, size_t v_i_1027_, lean_object* v_b_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_usize_dec_lt(v_i_1027_, v_sz_1026_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
lean_dec_ref(v___y_1032_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_b_1028_);
return v___x_1036_;
}
else
{
lean_object* v_snd_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1075_; 
v_snd_1037_ = lean_ctor_get(v_b_1028_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_b_1028_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_b_1028_, 0);
lean_dec(v_unused_1076_);
v___x_1039_ = v_b_1028_;
v_isShared_1040_ = v_isSharedCheck_1075_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_snd_1037_);
lean_dec(v_b_1028_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1075_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v_a_1043_; lean_object* v_a_1050_; 
v___x_1041_ = lean_box(0);
v_a_1050_ = lean_array_uget_borrowed(v_as_1025_, v_i_1027_);
if (lean_obj_tag(v_a_1050_) == 0)
{
v_a_1043_ = v_snd_1037_;
goto v___jp_1042_;
}
else
{
lean_object* v_val_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v_snd_1037_);
v_val_1051_ = lean_ctor_get(v_a_1050_, 0);
v___x_1052_ = l_Lean_LocalDecl_type(v_val_1051_);
lean_inc_ref(v___y_1032_);
v___x_1053_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1052_, v_includeDelayed_1022_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1053_) == 0)
{
uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec_ref(v___x_1053_);
v___x_1054_ = lean_nat_dec_eq(v___x_1023_, v___x_1024_);
v___x_1055_ = lean_box(0);
v___x_1056_ = l_Lean_LocalDecl_value_x3f(v_val_1051_, v___x_1054_);
if (lean_obj_tag(v___x_1056_) == 1)
{
lean_object* v_val_1057_; lean_object* v___x_1058_; 
v_val_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_val_1057_);
lean_dec_ref(v___x_1056_);
lean_inc_ref(v___y_1032_);
v___x_1058_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1057_, v_includeDelayed_1022_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_dec_ref(v___x_1058_);
v_a_1043_ = v___x_1055_;
goto v___jp_1042_;
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_del_object(v___x_1039_);
lean_dec_ref(v___y_1032_);
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
lean_dec(v___x_1056_);
v_a_1043_ = v___x_1055_;
goto v___jp_1042_;
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_del_object(v___x_1039_);
lean_dec_ref(v___y_1032_);
v_a_1067_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1053_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1053_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
v___jp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v_a_1043_);
lean_ctor_set(v___x_1039_, 0, v___x_1041_);
v___x_1045_ = v___x_1039_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_a_1043_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_add(v_i_1027_, v___x_1046_);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_1022_, v___x_1023_, v___x_1024_, v_as_1025_, v_sz_1026_, v___x_1047_, v___x_1045_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
return v___x_1048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(uint8_t v_includeDelayed_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v_inh_1080_, lean_object* v_n_1081_, lean_object* v_b_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
if (lean_obj_tag(v_n_1081_) == 0)
{
lean_object* v_cs_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1123_; 
v_cs_1089_ = lean_ctor_get(v_n_1081_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_n_1081_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1091_ = v_n_1081_;
v_isShared_1092_ = v_isSharedCheck_1123_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_cs_1089_);
lean_dec(v_n_1081_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1123_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; size_t v_sz_1095_; size_t v___x_1096_; lean_object* v___x_1097_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_b_1082_);
v_sz_1095_ = lean_array_size(v_cs_1089_);
v___x_1096_ = ((size_t)0ULL);
v___x_1097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_includeDelayed_1077_, v___x_1078_, v___x_1079_, v_inh_1080_, v_cs_1089_, v_sz_1095_, v___x_1096_, v___x_1094_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec_ref(v_cs_1089_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1114_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1114_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1114_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_fst_1102_; 
v_fst_1102_ = lean_ctor_get(v_a_1098_, 0);
if (lean_obj_tag(v_fst_1102_) == 0)
{
lean_object* v_snd_1103_; lean_object* v___x_1105_; 
v_snd_1103_ = lean_ctor_get(v_a_1098_, 1);
lean_inc(v_snd_1103_);
lean_dec(v_a_1098_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
lean_ctor_set(v___x_1091_, 0, v_snd_1103_);
v___x_1105_ = v___x_1091_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_snd_1103_);
v___x_1105_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1105_);
v___x_1107_ = v___x_1100_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
else
{
lean_object* v_val_1110_; lean_object* v___x_1112_; 
lean_inc_ref(v_fst_1102_);
lean_dec(v_a_1098_);
lean_del_object(v___x_1091_);
v_val_1110_ = lean_ctor_get(v_fst_1102_, 0);
lean_inc(v_val_1110_);
lean_dec_ref(v_fst_1102_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v_val_1110_);
v___x_1112_ = v___x_1100_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_val_1110_);
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
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_del_object(v___x_1091_);
v_a_1115_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1097_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1097_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
else
{
lean_object* v_vs_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1158_; 
v_vs_1124_ = lean_ctor_get(v_n_1081_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_n_1081_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1126_ = v_n_1081_;
v_isShared_1127_ = v_isSharedCheck_1158_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_vs_1124_);
lean_dec(v_n_1081_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1158_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; size_t v_sz_1130_; size_t v___x_1131_; lean_object* v___x_1132_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_b_1082_);
v_sz_1130_ = lean_array_size(v_vs_1124_);
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_1077_, v___x_1078_, v___x_1079_, v_vs_1124_, v_sz_1130_, v___x_1131_, v___x_1129_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec_ref(v_vs_1124_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1149_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1149_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1149_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_fst_1137_; 
v_fst_1137_ = lean_ctor_get(v_a_1133_, 0);
if (lean_obj_tag(v_fst_1137_) == 0)
{
lean_object* v_snd_1138_; lean_object* v___x_1140_; 
v_snd_1138_ = lean_ctor_get(v_a_1133_, 1);
lean_inc(v_snd_1138_);
lean_dec(v_a_1133_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v_snd_1138_);
v___x_1140_ = v___x_1126_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_snd_1138_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1140_);
v___x_1142_ = v___x_1135_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_object* v_val_1145_; lean_object* v___x_1147_; 
lean_inc_ref(v_fst_1137_);
lean_dec(v_a_1133_);
lean_del_object(v___x_1126_);
v_val_1145_ = lean_ctor_get(v_fst_1137_, 0);
lean_inc(v_val_1145_);
lean_dec_ref(v_fst_1137_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_val_1145_);
v___x_1147_ = v___x_1135_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_val_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_del_object(v___x_1126_);
v_a_1150_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1132_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1132_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(uint8_t v_includeDelayed_1159_, lean_object* v___x_1160_, lean_object* v___x_1161_, lean_object* v_as_1162_, size_t v_sz_1163_, size_t v_i_1164_, lean_object* v_b_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_usize_dec_lt(v_i_1164_, v_sz_1163_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref(v___y_1169_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_b_1165_);
return v___x_1173_;
}
else
{
lean_object* v_snd_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1212_; 
v_snd_1174_ = lean_ctor_get(v_b_1165_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_b_1165_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_b_1165_, 0);
lean_dec(v_unused_1213_);
v___x_1176_ = v_b_1165_;
v_isShared_1177_ = v_isSharedCheck_1212_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_snd_1174_);
lean_dec(v_b_1165_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1212_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v_a_1180_; lean_object* v_a_1187_; 
v___x_1178_ = lean_box(0);
v_a_1187_ = lean_array_uget_borrowed(v_as_1162_, v_i_1164_);
if (lean_obj_tag(v_a_1187_) == 0)
{
v_a_1180_ = v_snd_1174_;
goto v___jp_1179_;
}
else
{
lean_object* v_val_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_snd_1174_);
v_val_1188_ = lean_ctor_get(v_a_1187_, 0);
v___x_1189_ = l_Lean_LocalDecl_type(v_val_1188_);
lean_inc_ref(v___y_1169_);
v___x_1190_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1189_, v_includeDelayed_1159_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1190_) == 0)
{
uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v___x_1190_);
v___x_1191_ = lean_nat_dec_eq(v___x_1160_, v___x_1161_);
v___x_1192_ = lean_box(0);
v___x_1193_ = l_Lean_LocalDecl_value_x3f(v_val_1188_, v___x_1191_);
if (lean_obj_tag(v___x_1193_) == 1)
{
lean_object* v_val_1194_; lean_object* v___x_1195_; 
v_val_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_val_1194_);
lean_dec_ref(v___x_1193_);
lean_inc_ref(v___y_1169_);
v___x_1195_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1194_, v_includeDelayed_1159_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_dec_ref(v___x_1195_);
v_a_1180_ = v___x_1192_;
goto v___jp_1179_;
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1176_);
lean_dec_ref(v___y_1169_);
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
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
else
{
lean_dec(v___x_1193_);
v_a_1180_ = v___x_1192_;
goto v___jp_1179_;
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_del_object(v___x_1176_);
lean_dec_ref(v___y_1169_);
v_a_1204_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1190_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1190_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
v___jp_1179_:
{
lean_object* v___x_1182_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v_a_1180_);
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1182_ = v___x_1176_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_a_1180_);
v___x_1182_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
size_t v___x_1183_; size_t v___x_1184_; 
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1164_, v___x_1183_);
v_i_1164_ = v___x_1184_;
v_b_1165_ = v___x_1182_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(uint8_t v_includeDelayed_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v_as_1217_, size_t v_sz_1218_, size_t v_i_1219_, lean_object* v_b_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_usize_dec_lt(v_i_1219_, v_sz_1218_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v___y_1224_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_b_1220_);
return v___x_1228_;
}
else
{
lean_object* v_snd_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1267_; 
v_snd_1229_ = lean_ctor_get(v_b_1220_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_b_1220_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v_b_1220_, 0);
lean_dec(v_unused_1268_);
v___x_1231_ = v_b_1220_;
v_isShared_1232_ = v_isSharedCheck_1267_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_snd_1229_);
lean_dec(v_b_1220_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1267_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v_a_1235_; lean_object* v_a_1242_; 
v___x_1233_ = lean_box(0);
v_a_1242_ = lean_array_uget_borrowed(v_as_1217_, v_i_1219_);
if (lean_obj_tag(v_a_1242_) == 0)
{
v_a_1235_ = v_snd_1229_;
goto v___jp_1234_;
}
else
{
lean_object* v_val_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec(v_snd_1229_);
v_val_1243_ = lean_ctor_get(v_a_1242_, 0);
v___x_1244_ = l_Lean_LocalDecl_type(v_val_1243_);
lean_inc_ref(v___y_1224_);
v___x_1245_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v___x_1244_, v_includeDelayed_1214_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1245_) == 0)
{
uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec_ref(v___x_1245_);
v___x_1246_ = lean_nat_dec_eq(v___x_1215_, v___x_1216_);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Lean_LocalDecl_value_x3f(v_val_1243_, v___x_1246_);
if (lean_obj_tag(v___x_1248_) == 1)
{
lean_object* v_val_1249_; lean_object* v___x_1250_; 
v_val_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_val_1249_);
lean_dec_ref(v___x_1248_);
lean_inc_ref(v___y_1224_);
v___x_1250_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_val_1249_, v_includeDelayed_1214_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_dec_ref(v___x_1250_);
v_a_1235_ = v___x_1247_;
goto v___jp_1234_;
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_del_object(v___x_1231_);
lean_dec_ref(v___y_1224_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_dec(v___x_1248_);
v_a_1235_ = v___x_1247_;
goto v___jp_1234_;
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_del_object(v___x_1231_);
lean_dec_ref(v___y_1224_);
v_a_1259_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1245_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1245_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
v___jp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v_a_1235_);
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_a_1235_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1219_, v___x_1238_);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_1214_, v___x_1215_, v___x_1216_, v_as_1217_, v_sz_1218_, v___x_1239_, v___x_1237_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(uint8_t v_includeDelayed_1269_, lean_object* v___x_1270_, lean_object* v___x_1271_, lean_object* v_t_1272_, lean_object* v_init_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_root_1280_; lean_object* v_tail_1281_; lean_object* v___x_1282_; 
v_root_1280_ = lean_ctor_get(v_t_1272_, 0);
lean_inc_ref(v_root_1280_);
v_tail_1281_ = lean_ctor_get(v_t_1272_, 1);
lean_inc_ref(v_tail_1281_);
lean_dec_ref(v_t_1272_);
lean_inc_ref(v___y_1277_);
v___x_1282_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_includeDelayed_1269_, v___x_1270_, v___x_1271_, v_init_1273_, v_root_1280_, v_init_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1319_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1319_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1319_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
if (lean_obj_tag(v_a_1283_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; 
lean_dec_ref(v_tail_1281_);
lean_dec_ref(v___y_1277_);
v_a_1287_ = lean_ctor_get(v_a_1283_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v_a_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_a_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; size_t v_sz_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
lean_del_object(v___x_1285_);
v_a_1291_ = lean_ctor_get(v_a_1283_, 0);
lean_inc(v_a_1291_);
lean_dec_ref(v_a_1283_);
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v_a_1291_);
v_sz_1294_ = lean_array_size(v_tail_1281_);
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_1269_, v___x_1270_, v___x_1271_, v_tail_1281_, v_sz_1294_, v___x_1295_, v___x_1293_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec_ref(v_tail_1281_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1310_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1310_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1310_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_fst_1301_; 
v_fst_1301_ = lean_ctor_get(v_a_1297_, 0);
if (lean_obj_tag(v_fst_1301_) == 0)
{
lean_object* v_snd_1302_; lean_object* v___x_1304_; 
v_snd_1302_ = lean_ctor_get(v_a_1297_, 1);
lean_inc(v_snd_1302_);
lean_dec(v_a_1297_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_snd_1302_);
v___x_1304_ = v___x_1299_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_snd_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v_val_1306_; lean_object* v___x_1308_; 
lean_inc_ref(v_fst_1301_);
lean_dec(v_a_1297_);
v_val_1306_ = lean_ctor_get(v_fst_1301_, 0);
lean_inc(v_val_1306_);
lean_dec_ref(v_fst_1301_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_val_1306_);
v___x_1308_ = v___x_1299_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_val_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_a_1311_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1296_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1296_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_tail_1281_);
lean_dec_ref(v___y_1277_);
v_a_1320_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1282_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1282_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go(lean_object* v_mvarId_1328_, uint8_t v_includeDelayed_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_fileName_1336_; lean_object* v_fileMap_1337_; lean_object* v_options_1338_; lean_object* v_currRecDepth_1339_; lean_object* v_maxRecDepth_1340_; lean_object* v_ref_1341_; lean_object* v_currNamespace_1342_; lean_object* v_openDecls_1343_; lean_object* v_initHeartbeats_1344_; lean_object* v_maxHeartbeats_1345_; lean_object* v_quotContext_1346_; lean_object* v_currMacroScope_1347_; uint8_t v_diag_1348_; lean_object* v_cancelTk_x3f_1349_; uint8_t v_suppressElabErrors_1350_; lean_object* v_inheritedTraceOptions_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1418_; 
v_fileName_1336_ = lean_ctor_get(v_a_1333_, 0);
v_fileMap_1337_ = lean_ctor_get(v_a_1333_, 1);
v_options_1338_ = lean_ctor_get(v_a_1333_, 2);
v_currRecDepth_1339_ = lean_ctor_get(v_a_1333_, 3);
v_maxRecDepth_1340_ = lean_ctor_get(v_a_1333_, 4);
v_ref_1341_ = lean_ctor_get(v_a_1333_, 5);
v_currNamespace_1342_ = lean_ctor_get(v_a_1333_, 6);
v_openDecls_1343_ = lean_ctor_get(v_a_1333_, 7);
v_initHeartbeats_1344_ = lean_ctor_get(v_a_1333_, 8);
v_maxHeartbeats_1345_ = lean_ctor_get(v_a_1333_, 9);
v_quotContext_1346_ = lean_ctor_get(v_a_1333_, 10);
v_currMacroScope_1347_ = lean_ctor_get(v_a_1333_, 11);
v_diag_1348_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*14);
v_cancelTk_x3f_1349_ = lean_ctor_get(v_a_1333_, 12);
v_suppressElabErrors_1350_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1351_ = lean_ctor_get(v_a_1333_, 13);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_a_1333_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1353_ = v_a_1333_;
v_isShared_1354_ = v_isSharedCheck_1418_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_inheritedTraceOptions_1351_);
lean_inc(v_cancelTk_x3f_1349_);
lean_inc(v_currMacroScope_1347_);
lean_inc(v_quotContext_1346_);
lean_inc(v_maxHeartbeats_1345_);
lean_inc(v_initHeartbeats_1344_);
lean_inc(v_openDecls_1343_);
lean_inc(v_currNamespace_1342_);
lean_inc(v_ref_1341_);
lean_inc(v_maxRecDepth_1340_);
lean_inc(v_currRecDepth_1339_);
lean_inc(v_options_1338_);
lean_inc(v_fileMap_1337_);
lean_inc(v_fileName_1336_);
lean_dec(v_a_1333_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1418_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_nat_dec_eq(v_currRecDepth_1339_, v_maxRecDepth_1340_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_add(v_currRecDepth_1339_, v___x_1356_);
lean_inc(v_maxRecDepth_1340_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 3, v___x_1357_);
v___x_1359_ = v___x_1353_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_fileName_1336_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_fileMap_1337_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_options_1338_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_maxRecDepth_1340_);
lean_ctor_set(v_reuseFailAlloc_1416_, 5, v_ref_1341_);
lean_ctor_set(v_reuseFailAlloc_1416_, 6, v_currNamespace_1342_);
lean_ctor_set(v_reuseFailAlloc_1416_, 7, v_openDecls_1343_);
lean_ctor_set(v_reuseFailAlloc_1416_, 8, v_initHeartbeats_1344_);
lean_ctor_set(v_reuseFailAlloc_1416_, 9, v_maxHeartbeats_1345_);
lean_ctor_set(v_reuseFailAlloc_1416_, 10, v_quotContext_1346_);
lean_ctor_set(v_reuseFailAlloc_1416_, 11, v_currMacroScope_1347_);
lean_ctor_set(v_reuseFailAlloc_1416_, 12, v_cancelTk_x3f_1349_);
lean_ctor_set(v_reuseFailAlloc_1416_, 13, v_inheritedTraceOptions_1351_);
lean_ctor_set_uint8(v_reuseFailAlloc_1416_, sizeof(void*)*14, v_diag_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1416_, sizeof(void*)*14 + 1, v_suppressElabErrors_1350_);
v___x_1359_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; 
lean_inc(v_mvarId_1328_);
v___x_1360_ = l_Lean_MVarId_getDecl(v_mvarId_1328_, v_a_1331_, v_a_1332_, v___x_1359_, v_a_1334_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_lctx_1362_; lean_object* v_type_1363_; lean_object* v___x_1364_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
v_lctx_1362_ = lean_ctor_get(v_a_1361_, 1);
lean_inc_ref(v_lctx_1362_);
v_type_1363_ = lean_ctor_get(v_a_1361_, 2);
lean_inc_ref(v_type_1363_);
lean_dec(v_a_1361_);
lean_inc_ref(v___x_1359_);
v___x_1364_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_type_1363_, v_includeDelayed_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v___x_1359_, v_a_1334_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_decls_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec_ref(v___x_1364_);
v_decls_1365_ = lean_ctor_get(v_lctx_1362_, 1);
lean_inc_ref(v_decls_1365_);
lean_dec_ref(v_lctx_1362_);
v___x_1366_ = lean_box(0);
lean_inc_ref(v___x_1359_);
v___x_1367_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_1329_, v_currRecDepth_1339_, v_maxRecDepth_1340_, v_decls_1365_, v___x_1366_, v_a_1330_, v_a_1331_, v_a_1332_, v___x_1359_, v_a_1334_);
lean_dec(v_maxRecDepth_1340_);
lean_dec(v_currRecDepth_1339_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
lean_dec_ref(v___x_1367_);
v___x_1368_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1328_, v_a_1332_);
lean_dec(v_mvarId_1328_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1399_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1399_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1399_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
if (lean_obj_tag(v_a_1369_) == 1)
{
lean_object* v_val_1373_; lean_object* v_mvarIdPending_1374_; uint8_t v_a_1381_; lean_object* v___x_1383_; 
lean_del_object(v___x_1371_);
v_val_1373_ = lean_ctor_get(v_a_1369_, 0);
lean_inc(v_val_1373_);
lean_dec_ref(v_a_1369_);
v_mvarIdPending_1374_ = lean_ctor_get(v_val_1373_, 1);
lean_inc(v_mvarIdPending_1374_);
lean_dec(v_val_1373_);
v___x_1383_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarIdPending_1374_, v_a_1332_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; uint8_t v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = lean_unbox(v_a_1384_);
lean_dec(v_a_1384_);
if (v___x_1385_ == 0)
{
goto v___jp_1375_;
}
else
{
v_a_1381_ = v___x_1355_;
goto v___jp_1380_;
}
}
else
{
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1386_; uint8_t v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1383_);
v___x_1387_ = lean_unbox(v_a_1386_);
lean_dec(v_a_1386_);
v_a_1381_ = v___x_1387_;
goto v___jp_1380_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_mvarIdPending_1374_);
lean_dec_ref(v___x_1359_);
v_a_1388_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1383_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1383_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
v___jp_1375_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = lean_st_ref_take(v_a_1330_);
lean_inc(v_mvarIdPending_1374_);
v___x_1377_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_1376_, v_mvarIdPending_1374_, v___x_1366_);
v___x_1378_ = lean_st_ref_set(v_a_1330_, v___x_1377_);
v_mvarId_1328_ = v_mvarIdPending_1374_;
v_a_1333_ = v___x_1359_;
goto _start;
}
v___jp_1380_:
{
if (v_a_1381_ == 0)
{
v_mvarId_1328_ = v_mvarIdPending_1374_;
v_a_1333_ = v___x_1359_;
goto _start;
}
else
{
goto v___jp_1375_;
}
}
}
else
{
lean_object* v___x_1397_; 
lean_dec(v_a_1369_);
lean_dec_ref(v___x_1359_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1366_);
v___x_1397_ = v___x_1371_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1366_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v___x_1359_);
v_a_1400_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1368_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1368_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_dec_ref(v___x_1359_);
lean_dec(v_mvarId_1328_);
return v___x_1367_;
}
}
else
{
lean_dec_ref(v_lctx_1362_);
lean_dec_ref(v___x_1359_);
lean_dec(v_maxRecDepth_1340_);
lean_dec(v_currRecDepth_1339_);
lean_dec(v_mvarId_1328_);
return v___x_1364_;
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v___x_1359_);
lean_dec(v_maxRecDepth_1340_);
lean_dec(v_currRecDepth_1339_);
lean_dec(v_mvarId_1328_);
v_a_1408_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1360_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1360_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
else
{
lean_object* v___x_1417_; 
lean_del_object(v___x_1353_);
lean_dec_ref(v_inheritedTraceOptions_1351_);
lean_dec(v_cancelTk_x3f_1349_);
lean_dec(v_currMacroScope_1347_);
lean_dec(v_quotContext_1346_);
lean_dec(v_maxHeartbeats_1345_);
lean_dec(v_initHeartbeats_1344_);
lean_dec(v_openDecls_1343_);
lean_dec(v_currNamespace_1342_);
lean_dec(v_maxRecDepth_1340_);
lean_dec(v_currRecDepth_1339_);
lean_dec_ref(v_options_1338_);
lean_dec_ref(v_fileMap_1337_);
lean_dec_ref(v_fileName_1336_);
lean_dec(v_mvarId_1328_);
v___x_1417_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1341_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(lean_object* v_as_1419_, size_t v_i_1420_, size_t v_stop_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_usize_dec_eq(v_i_1420_, v_stop_1421_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_array_uget_borrowed(v_as_1419_, v_i_1420_);
lean_inc_ref(v___y_1426_);
lean_inc(v___x_1430_);
v___x_1431_ = l___private_Lean_Meta_CollectMVars_0__go(v___x_1430_, v___x_1429_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; size_t v___x_1433_; size_t v___x_1434_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1420_, v___x_1433_);
v_i_1420_ = v___x_1434_;
v_b_1422_ = v_a_1432_;
goto _start;
}
else
{
lean_dec_ref(v___y_1426_);
return v___x_1431_;
}
}
else
{
lean_object* v___x_1436_; 
lean_dec_ref(v___y_1426_);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_b_1422_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(lean_object* v_as_1437_, lean_object* v_i_1438_, lean_object* v_stop_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
size_t v_i_boxed_1447_; size_t v_stop_boxed_1448_; lean_object* v_res_1449_; 
v_i_boxed_1447_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_stop_boxed_1448_ = lean_unbox_usize(v_stop_1439_);
lean_dec(v_stop_1439_);
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_as_1437_, v_i_boxed_1447_, v_stop_boxed_1448_, v_b_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v_as_1437_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(lean_object* v_includeDelayed_1450_, lean_object* v___x_1451_, lean_object* v___x_1452_, lean_object* v_inh_1453_, lean_object* v_as_1454_, lean_object* v_sz_1455_, lean_object* v_i_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v_includeDelayed_boxed_1464_; size_t v_sz_boxed_1465_; size_t v_i_boxed_1466_; lean_object* v_res_1467_; 
v_includeDelayed_boxed_1464_ = lean_unbox(v_includeDelayed_1450_);
v_sz_boxed_1465_ = lean_unbox_usize(v_sz_1455_);
lean_dec(v_sz_1455_);
v_i_boxed_1466_ = lean_unbox_usize(v_i_1456_);
lean_dec(v_i_1456_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_includeDelayed_boxed_1464_, v___x_1451_, v___x_1452_, v_inh_1453_, v_as_1454_, v_sz_boxed_1465_, v_i_boxed_1466_, v_b_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v_as_1454_);
lean_dec(v___x_1452_);
lean_dec(v___x_1451_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(lean_object* v_includeDelayed_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v_t_1471_, lean_object* v_init_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
uint8_t v_includeDelayed_boxed_1479_; lean_object* v_res_1480_; 
v_includeDelayed_boxed_1479_ = lean_unbox(v_includeDelayed_1468_);
v_res_1480_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_boxed_1479_, v___x_1469_, v___x_1470_, v_t_1471_, v_init_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v___x_1470_);
lean_dec(v___x_1469_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(lean_object* v_includeDelayed_1481_, lean_object* v___x_1482_, lean_object* v___x_1483_, lean_object* v_as_1484_, lean_object* v_sz_1485_, lean_object* v_i_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v_includeDelayed_boxed_1494_; size_t v_sz_boxed_1495_; size_t v_i_boxed_1496_; lean_object* v_res_1497_; 
v_includeDelayed_boxed_1494_ = lean_unbox(v_includeDelayed_1481_);
v_sz_boxed_1495_ = lean_unbox_usize(v_sz_1485_);
lean_dec(v_sz_1485_);
v_i_boxed_1496_ = lean_unbox_usize(v_i_1486_);
lean_dec(v_i_1486_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_boxed_1494_, v___x_1482_, v___x_1483_, v_as_1484_, v_sz_boxed_1495_, v_i_boxed_1496_, v_b_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v_as_1484_);
lean_dec(v___x_1483_);
lean_dec(v___x_1482_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(lean_object* v_includeDelayed_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, lean_object* v_as_1501_, lean_object* v_sz_1502_, lean_object* v_i_1503_, lean_object* v_b_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v_includeDelayed_boxed_1511_; size_t v_sz_boxed_1512_; size_t v_i_boxed_1513_; lean_object* v_res_1514_; 
v_includeDelayed_boxed_1511_ = lean_unbox(v_includeDelayed_1498_);
v_sz_boxed_1512_ = lean_unbox_usize(v_sz_1502_);
lean_dec(v_sz_1502_);
v_i_boxed_1513_ = lean_unbox_usize(v_i_1503_);
lean_dec(v_i_1503_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_boxed_1511_, v___x_1499_, v___x_1500_, v_as_1501_, v_sz_boxed_1512_, v_i_boxed_1513_, v_b_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v_as_1501_);
lean_dec(v___x_1500_);
lean_dec(v___x_1499_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(lean_object* v_includeDelayed_1515_, lean_object* v___x_1516_, lean_object* v___x_1517_, lean_object* v_as_1518_, lean_object* v_sz_1519_, lean_object* v_i_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
uint8_t v_includeDelayed_boxed_1528_; size_t v_sz_boxed_1529_; size_t v_i_boxed_1530_; lean_object* v_res_1531_; 
v_includeDelayed_boxed_1528_ = lean_unbox(v_includeDelayed_1515_);
v_sz_boxed_1529_ = lean_unbox_usize(v_sz_1519_);
lean_dec(v_sz_1519_);
v_i_boxed_1530_ = lean_unbox_usize(v_i_1520_);
lean_dec(v_i_1520_);
v_res_1531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_boxed_1528_, v___x_1516_, v___x_1517_, v_as_1518_, v_sz_boxed_1529_, v_i_boxed_1530_, v_b_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v_as_1518_);
lean_dec(v___x_1517_);
lean_dec(v___x_1516_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(lean_object* v_includeDelayed_1532_, lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v_as_1535_, lean_object* v_sz_1536_, lean_object* v_i_1537_, lean_object* v_b_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v_includeDelayed_boxed_1545_; size_t v_sz_boxed_1546_; size_t v_i_boxed_1547_; lean_object* v_res_1548_; 
v_includeDelayed_boxed_1545_ = lean_unbox(v_includeDelayed_1532_);
v_sz_boxed_1546_ = lean_unbox_usize(v_sz_1536_);
lean_dec(v_sz_1536_);
v_i_boxed_1547_ = lean_unbox_usize(v_i_1537_);
lean_dec(v_i_1537_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_boxed_1545_, v___x_1533_, v___x_1534_, v_as_1535_, v_sz_boxed_1546_, v_i_boxed_1547_, v_b_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v_as_1535_);
lean_dec(v___x_1534_);
lean_dec(v___x_1533_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(lean_object* v_includeDelayed_1549_, lean_object* v___x_1550_, lean_object* v___x_1551_, lean_object* v_inh_1552_, lean_object* v_n_1553_, lean_object* v_b_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v_includeDelayed_boxed_1561_; lean_object* v_res_1562_; 
v_includeDelayed_boxed_1561_ = lean_unbox(v_includeDelayed_1549_);
v_res_1562_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_includeDelayed_boxed_1561_, v___x_1550_, v___x_1551_, v_inh_1552_, v_n_1553_, v_b_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec(v___x_1551_);
lean_dec(v___x_1550_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(lean_object* v_e_1563_, lean_object* v_includeDelayed_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
uint8_t v_includeDelayed_boxed_1571_; lean_object* v_res_1572_; 
v_includeDelayed_boxed_1571_ = lean_unbox(v_includeDelayed_1564_);
v_res_1572_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1563_, v_includeDelayed_boxed_1571_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CollectMVars_0__go___boxed(lean_object* v_mvarId_1573_, lean_object* v_includeDelayed_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
uint8_t v_includeDelayed_boxed_1581_; lean_object* v_res_1582_; 
v_includeDelayed_boxed_1581_ = lean_unbox(v_includeDelayed_1574_);
v_res_1582_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1573_, v_includeDelayed_boxed_1581_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
lean_dec(v_a_1579_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(lean_object* v_mvarId_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_1583_, v___y_1586_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(lean_object* v_mvarId_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(v_mvarId_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec(v_mvarId_1591_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(lean_object* v_00_u03b1_1599_, lean_object* v_ref_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_1600_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(lean_object* v_00_u03b1_1608_, lean_object* v_ref_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(v_00_u03b1_1608_, v_ref_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(lean_object* v_00_u03b2_1617_, lean_object* v_m_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_1618_, v_a_1619_, v_b_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(lean_object* v_mvarId_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_1622_, v___y_1625_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(lean_object* v_mvarId_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_mvarId_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec(v_mvarId_1630_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(lean_object* v_mvarId_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_1638_, v___y_1641_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(lean_object* v_mvarId_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec(v_mvarId_1646_);
return v_res_1653_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(lean_object* v_00_u03b2_1654_, lean_object* v_a_1655_, lean_object* v_x_1656_){
_start:
{
uint8_t v___x_1657_; 
v___x_1657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_1655_, v_x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1658_, lean_object* v_a_1659_, lean_object* v_x_1660_){
_start:
{
uint8_t v_res_1661_; lean_object* v_r_1662_; 
v_res_1661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(v_00_u03b2_1658_, v_a_1659_, v_x_1660_);
lean_dec(v_x_1660_);
lean_dec(v_a_1659_);
v_r_1662_ = lean_box(v_res_1661_);
return v_r_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1(lean_object* v_00_u03b2_1663_, lean_object* v_data_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_data_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1666_, lean_object* v_i_1667_, lean_object* v_source_1668_, lean_object* v_target_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v_i_1667_, v_source_1668_, v_target_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_x_1672_, v_x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies(lean_object* v_mvarId_1675_, uint8_t v_includeDelayed_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1683_ = lean_st_mk_ref(v___x_1682_);
v___x_1684_ = l___private_Lean_Meta_CollectMVars_0__go(v_mvarId_1675_, v_includeDelayed_1676_, v___x_1683_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v___x_1684_, 0);
lean_dec(v_unused_1693_);
v___x_1686_ = v___x_1684_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_dec(v___x_1684_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_st_ref_get(v___x_1683_);
lean_dec(v___x_1683_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v___x_1683_);
v_a_1694_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1684_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1684_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object* v_mvarId_1702_, lean_object* v_includeDelayed_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
uint8_t v_includeDelayed_boxed_1709_; lean_object* v_res_1710_; 
v_includeDelayed_boxed_1709_ = lean_unbox(v_includeDelayed_1703_);
v_res_1710_ = l_Lean_MVarId_getMVarDependencies(v_mvarId_1702_, v_includeDelayed_boxed_1709_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies(lean_object* v_e_1711_, uint8_t v_includeDelayed_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_obj_once(&l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1, &l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once, _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1);
v___x_1719_ = lean_st_mk_ref(v___x_1718_);
v___x_1720_ = l___private_Lean_Meta_CollectMVars_0__addMVars(v_e_1711_, v_includeDelayed_1712_, v___x_1719_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1728_; 
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v___x_1720_, 0);
lean_dec(v_unused_1729_);
v___x_1722_ = v___x_1720_;
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
else
{
lean_dec(v___x_1720_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = lean_st_ref_get(v___x_1719_);
lean_dec(v___x_1719_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1724_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v___x_1719_);
v_a_1730_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1720_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1720_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getMVarDependencies___boxed(lean_object* v_e_1738_, lean_object* v_includeDelayed_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
uint8_t v_includeDelayed_boxed_1745_; lean_object* v_res_1746_; 
v_includeDelayed_boxed_1745_ = lean_unbox(v_includeDelayed_1739_);
v_res_1746_ = l_Lean_Expr_getMVarDependencies(v_e_1738_, v_includeDelayed_boxed_1745_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
lean_dec(v_a_1743_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
return v_res_1746_;
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
