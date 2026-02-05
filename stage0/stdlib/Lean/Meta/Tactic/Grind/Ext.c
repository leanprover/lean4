// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Ext
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.SynthInstance
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "failed to synthesize instance when instantiating extensionality theorem `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__1_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__3_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceAndAssign___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to apply extensionality theorem `"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__0_value;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\nresulting terms contain metavariables"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__2_value;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__5_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(189, 159, 161, 247, 89, 7, 26, 174)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__7_value;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\nis not definitionally equal to"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__9_value;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__14_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static uint64_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__17;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getMaxGeneration___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = lean_apply_11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed), 12, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_7);
lean_closure_set(x_14, 6, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_14, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
x_16 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_5, x_4);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_27 = x_6;
} else {
 lean_dec_ref(x_6);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 2);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_27)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_27;
}
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_26);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_inc(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_26, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_26, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_26, 0);
lean_dec(x_38);
x_39 = lean_array_uget(x_3, x_5);
x_40 = l_Lean_Expr_mvarId_x21(x_39);
x_41 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(x_40, x_14);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_54; uint8_t x_85; uint8_t x_86; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_array_fget(x_28, x_29);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_29, x_45);
lean_dec(x_29);
lean_ctor_set(x_26, 1, x_46);
x_85 = lean_unbox(x_44);
lean_dec(x_44);
x_86 = l_Lean_BinderInfo_isInstImplicit(x_85);
if (x_86 == 0)
{
lean_dec(x_42);
x_54 = x_86;
goto block_84;
}
else
{
uint8_t x_87; 
x_87 = lean_unbox(x_42);
lean_dec(x_42);
if (x_87 == 0)
{
x_54 = x_86;
goto block_84;
}
else
{
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_27);
goto block_53;
}
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__0));
if (lean_is_scalar(x_27)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_27;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_26);
if (lean_is_scalar(x_43)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_43;
}
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
block_53:
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_31);
lean_ctor_set(x_52, 1, x_26);
x_18 = x_52;
x_19 = lean_box(0);
goto block_23;
}
block_84:
{
if (x_54 == 0)
{
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_27);
goto block_53;
}
else
{
lean_object* x_55; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_39);
x_55 = lean_infer_type(x_39, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_57 = l_Lean_Meta_Grind_synthInstanceAndAssign___redArg(x_39, x_56, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Meta_Grind_getConfig___redArg(x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get_uint8(x_61, sizeof(void*)*11 + 14);
lean_dec(x_61);
if (x_62 == 0)
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
goto block_51;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__2;
x_64 = l_Lean_MessageData_ofName(x_1);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_indentExpr(x_2);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_Grind_reportIssue(x_69, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
x_47 = lean_box(0);
goto block_51;
}
else
{
uint8_t x_71; 
lean_dec_ref(x_26);
lean_dec(x_43);
lean_dec(x_27);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec_ref(x_26);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
lean_dec(x_60);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_43);
lean_dec(x_27);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_31);
lean_ctor_set(x_77, 1, x_26);
x_18 = x_77;
x_19 = lean_box(0);
goto block_23;
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_26);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_57);
if (x_78 == 0)
{
return x_57;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_57, 0);
lean_inc(x_79);
lean_dec(x_57);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_26);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_55);
if (x_81 == 0)
{
return x_55;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_55, 0);
lean_inc(x_82);
lean_dec(x_55);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_39);
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_41);
if (x_88 == 0)
{
return x_41;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_41, 0);
lean_inc(x_89);
lean_dec(x_41);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_26);
x_91 = lean_array_uget(x_3, x_5);
x_92 = l_Lean_Expr_mvarId_x21(x_91);
x_93 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(x_92, x_14);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_107; uint8_t x_138; uint8_t x_139; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = lean_array_fget(x_28, x_29);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_29, x_97);
lean_dec(x_29);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_28);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_30);
x_138 = lean_unbox(x_96);
lean_dec(x_96);
x_139 = l_Lean_BinderInfo_isInstImplicit(x_138);
if (x_139 == 0)
{
lean_dec(x_94);
x_107 = x_139;
goto block_137;
}
else
{
uint8_t x_140; 
x_140 = lean_unbox(x_94);
lean_dec(x_94);
if (x_140 == 0)
{
x_107 = x_139;
goto block_137;
}
else
{
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_27);
goto block_106;
}
}
block_104:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__0));
if (lean_is_scalar(x_27)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_27;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
if (lean_is_scalar(x_95)) {
 x_103 = lean_alloc_ctor(0, 1, 0);
} else {
 x_103 = x_95;
}
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
block_106:
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_31);
lean_ctor_set(x_105, 1, x_99);
x_18 = x_105;
x_19 = lean_box(0);
goto block_23;
}
block_137:
{
if (x_107 == 0)
{
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_27);
goto block_106;
}
else
{
lean_object* x_108; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_91);
x_108 = lean_infer_type(x_91, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_110 = l_Lean_Meta_Grind_synthInstanceAndAssign___redArg(x_91, x_109, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = l_Lean_Meta_Grind_getConfig___redArg(x_9);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = lean_ctor_get_uint8(x_114, sizeof(void*)*11 + 14);
lean_dec(x_114);
if (x_115 == 0)
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_100 = lean_box(0);
goto block_104;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__2;
x_117 = l_Lean_MessageData_ofName(x_1);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_indentExpr(x_2);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Meta_Grind_reportIssue(x_122, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_123) == 0)
{
lean_dec_ref(x_123);
x_100 = lean_box(0);
goto block_104;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_27);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_127 = lean_ctor_get(x_113, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_128 = x_113;
} else {
 lean_dec_ref(x_113);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
}
else
{
lean_object* x_130; 
lean_dec(x_95);
lean_dec(x_27);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_31);
lean_ctor_set(x_130, 1, x_99);
x_18 = x_130;
x_19 = lean_box(0);
goto block_23;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_131 = lean_ctor_get(x_110, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_132 = x_110;
} else {
 lean_dec_ref(x_110);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_99);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_108, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_135 = x_108;
} else {
 lean_dec_ref(x_108);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
return x_136;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_91);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_93, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_142 = x_93;
} else {
 lean_dec_ref(x_93);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_141);
return x_143;
}
}
}
}
block_23:
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__5(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_eq(x_2, x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_27; lean_object* x_28; 
x_23 = lean_array_uget(x_1, x_2);
x_27 = l_Lean_Expr_mvarId_x21(x_23);
x_28 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(x_27, x_12);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
x_24 = lean_box(0);
goto block_26;
}
else
{
lean_dec(x_23);
x_16 = x_4;
x_17 = lean_box(0);
goto block_21;
}
}
else
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_dec(x_23);
x_16 = x_4;
x_17 = lean_box(0);
goto block_21;
}
else
{
x_24 = lean_box(0);
goto block_26;
}
}
else
{
uint8_t x_33; 
lean_dec(x_23);
lean_dec_ref(x_4);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
block_26:
{
lean_object* x_25; 
x_25 = lean_array_push(x_4, x_23);
x_16 = x_25;
x_17 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_4);
return x_36;
}
block_21:
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_18;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__14));
x_2 = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__13));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__17() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_18; lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_Meta_Grind_getMaxGeneration___redArg(x_5);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_nat_dec_lt(x_23, x_26);
lean_dec(x_26);
lean_dec(x_23);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_110; 
lean_free_object(x_24);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec_ref(x_2);
lean_inc_ref(x_11);
lean_inc(x_29);
x_110 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_29, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_356; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_111);
x_356 = lean_infer_type(x_111, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
lean_dec_ref(x_356);
x_358 = l_Lean_Meta_Context_config(x_9);
x_359 = !lean_is_exclusive(x_358);
if (x_359 == 0)
{
uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; uint8_t x_370; uint64_t x_371; uint64_t x_372; uint64_t x_373; lean_object* x_374; uint8_t x_375; uint64_t x_376; uint64_t x_377; uint64_t x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_360 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
x_361 = lean_ctor_get(x_9, 1);
x_362 = lean_ctor_get(x_9, 2);
x_363 = lean_ctor_get(x_9, 3);
x_364 = lean_ctor_get(x_9, 4);
x_365 = lean_ctor_get(x_9, 5);
x_366 = lean_ctor_get(x_9, 6);
x_367 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 1);
x_368 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 2);
x_369 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 3);
x_370 = 1;
lean_ctor_set_uint8(x_358, 9, x_370);
x_371 = l_Lean_Meta_Context_configKey(x_9);
x_372 = 2;
x_373 = lean_uint64_shift_right(x_371, x_372);
x_374 = lean_box(0);
x_375 = 0;
x_376 = lean_uint64_shift_left(x_373, x_372);
x_377 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__17;
x_378 = lean_uint64_lor(x_376, x_377);
x_379 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_379, 0, x_358);
lean_ctor_set_uint64(x_379, sizeof(void*)*1, x_378);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc_ref(x_363);
lean_inc_ref(x_362);
lean_inc(x_361);
x_380 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_361);
lean_ctor_set(x_380, 2, x_362);
lean_ctor_set(x_380, 3, x_363);
lean_ctor_set(x_380, 4, x_364);
lean_ctor_set(x_380, 5, x_365);
lean_ctor_set(x_380, 6, x_366);
lean_ctor_set_uint8(x_380, sizeof(void*)*7, x_360);
lean_ctor_set_uint8(x_380, sizeof(void*)*7 + 1, x_367);
lean_ctor_set_uint8(x_380, sizeof(void*)*7 + 2, x_368);
lean_ctor_set_uint8(x_380, sizeof(void*)*7 + 3, x_369);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
x_381 = l_Lean_Meta_forallMetaTelescopeReducing(x_357, x_374, x_375, x_380, x_10, x_11, x_12);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec_ref(x_381);
x_112 = x_382;
x_113 = lean_box(0);
goto block_355;
}
else
{
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
lean_dec_ref(x_381);
x_112 = x_383;
x_113 = lean_box(0);
goto block_355;
}
else
{
uint8_t x_384; 
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_384 = !lean_is_exclusive(x_381);
if (x_384 == 0)
{
return x_381;
}
else
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_ctor_get(x_381, 0);
lean_inc(x_385);
lean_dec(x_381);
x_386 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_386, 0, x_385);
return x_386;
}
}
}
}
else
{
uint8_t x_387; uint8_t x_388; uint8_t x_389; uint8_t x_390; uint8_t x_391; uint8_t x_392; uint8_t x_393; uint8_t x_394; uint8_t x_395; uint8_t x_396; uint8_t x_397; uint8_t x_398; uint8_t x_399; uint8_t x_400; uint8_t x_401; uint8_t x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; uint8_t x_413; uint8_t x_414; uint8_t x_415; lean_object* x_416; uint64_t x_417; uint64_t x_418; uint64_t x_419; lean_object* x_420; uint8_t x_421; uint64_t x_422; uint64_t x_423; uint64_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_387 = lean_ctor_get_uint8(x_358, 0);
x_388 = lean_ctor_get_uint8(x_358, 1);
x_389 = lean_ctor_get_uint8(x_358, 2);
x_390 = lean_ctor_get_uint8(x_358, 3);
x_391 = lean_ctor_get_uint8(x_358, 4);
x_392 = lean_ctor_get_uint8(x_358, 5);
x_393 = lean_ctor_get_uint8(x_358, 6);
x_394 = lean_ctor_get_uint8(x_358, 7);
x_395 = lean_ctor_get_uint8(x_358, 8);
x_396 = lean_ctor_get_uint8(x_358, 10);
x_397 = lean_ctor_get_uint8(x_358, 11);
x_398 = lean_ctor_get_uint8(x_358, 12);
x_399 = lean_ctor_get_uint8(x_358, 13);
x_400 = lean_ctor_get_uint8(x_358, 14);
x_401 = lean_ctor_get_uint8(x_358, 15);
x_402 = lean_ctor_get_uint8(x_358, 16);
x_403 = lean_ctor_get_uint8(x_358, 17);
x_404 = lean_ctor_get_uint8(x_358, 18);
lean_dec(x_358);
x_405 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
x_406 = lean_ctor_get(x_9, 1);
x_407 = lean_ctor_get(x_9, 2);
x_408 = lean_ctor_get(x_9, 3);
x_409 = lean_ctor_get(x_9, 4);
x_410 = lean_ctor_get(x_9, 5);
x_411 = lean_ctor_get(x_9, 6);
x_412 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 1);
x_413 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 2);
x_414 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 3);
x_415 = 1;
x_416 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_416, 0, x_387);
lean_ctor_set_uint8(x_416, 1, x_388);
lean_ctor_set_uint8(x_416, 2, x_389);
lean_ctor_set_uint8(x_416, 3, x_390);
lean_ctor_set_uint8(x_416, 4, x_391);
lean_ctor_set_uint8(x_416, 5, x_392);
lean_ctor_set_uint8(x_416, 6, x_393);
lean_ctor_set_uint8(x_416, 7, x_394);
lean_ctor_set_uint8(x_416, 8, x_395);
lean_ctor_set_uint8(x_416, 9, x_415);
lean_ctor_set_uint8(x_416, 10, x_396);
lean_ctor_set_uint8(x_416, 11, x_397);
lean_ctor_set_uint8(x_416, 12, x_398);
lean_ctor_set_uint8(x_416, 13, x_399);
lean_ctor_set_uint8(x_416, 14, x_400);
lean_ctor_set_uint8(x_416, 15, x_401);
lean_ctor_set_uint8(x_416, 16, x_402);
lean_ctor_set_uint8(x_416, 17, x_403);
lean_ctor_set_uint8(x_416, 18, x_404);
x_417 = l_Lean_Meta_Context_configKey(x_9);
x_418 = 2;
x_419 = lean_uint64_shift_right(x_417, x_418);
x_420 = lean_box(0);
x_421 = 0;
x_422 = lean_uint64_shift_left(x_419, x_418);
x_423 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__17;
x_424 = lean_uint64_lor(x_422, x_423);
x_425 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_425, 0, x_416);
lean_ctor_set_uint64(x_425, sizeof(void*)*1, x_424);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
lean_inc_ref(x_408);
lean_inc_ref(x_407);
lean_inc(x_406);
x_426 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_406);
lean_ctor_set(x_426, 2, x_407);
lean_ctor_set(x_426, 3, x_408);
lean_ctor_set(x_426, 4, x_409);
lean_ctor_set(x_426, 5, x_410);
lean_ctor_set(x_426, 6, x_411);
lean_ctor_set_uint8(x_426, sizeof(void*)*7, x_405);
lean_ctor_set_uint8(x_426, sizeof(void*)*7 + 1, x_412);
lean_ctor_set_uint8(x_426, sizeof(void*)*7 + 2, x_413);
lean_ctor_set_uint8(x_426, sizeof(void*)*7 + 3, x_414);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
x_427 = l_Lean_Meta_forallMetaTelescopeReducing(x_357, x_420, x_421, x_426, x_10, x_11, x_12);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
lean_dec_ref(x_427);
x_112 = x_428;
x_113 = lean_box(0);
goto block_355;
}
else
{
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_427, 0);
lean_inc(x_429);
lean_dec_ref(x_427);
x_112 = x_429;
x_113 = lean_box(0);
goto block_355;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_430 = lean_ctor_get(x_427, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_431 = x_427;
} else {
 lean_dec_ref(x_427);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_430);
return x_432;
}
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_433 = !lean_is_exclusive(x_356);
if (x_433 == 0)
{
return x_356;
}
else
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_356, 0);
lean_inc(x_434);
lean_dec(x_356);
x_435 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
}
block_355:
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_112, 1);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 0);
x_118 = lean_ctor_get(x_115, 0);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_119);
lean_inc_ref(x_1);
x_120 = l_Lean_Meta_isExprDefEq(x_1, x_119, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_3);
x_123 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_ctor_get_uint8(x_124, sizeof(void*)*11 + 14);
lean_dec(x_124);
if (x_125 == 0)
{
lean_free_object(x_115);
lean_dec(x_119);
lean_free_object(x_112);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_126 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1;
x_127 = l_Lean_MessageData_ofName(x_29);
lean_ctor_set_tag(x_115, 7);
lean_ctor_set(x_115, 1, x_127);
lean_ctor_set(x_115, 0, x_126);
x_128 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
lean_ctor_set_tag(x_112, 7);
lean_ctor_set(x_112, 1, x_128);
lean_ctor_set(x_112, 0, x_115);
x_129 = l_Lean_indentExpr(x_1);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_112);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_indentExpr(x_119);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Meta_Grind_reportIssue(x_134, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_135) == 0)
{
lean_dec_ref(x_135);
x_14 = lean_box(0);
goto block_17;
}
else
{
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_free_object(x_115);
lean_dec(x_119);
lean_free_object(x_112);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_136 = !lean_is_exclusive(x_123);
if (x_136 == 0)
{
return x_123;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_123, 0);
lean_inc(x_137);
lean_dec(x_123);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; lean_object* x_145; 
lean_dec(x_119);
lean_free_object(x_112);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_array_get_size(x_118);
x_141 = l_Array_toSubarray___redArg(x_118, x_139, x_140);
x_142 = lean_box(0);
lean_ctor_set(x_115, 1, x_141);
lean_ctor_set(x_115, 0, x_142);
x_143 = lean_array_size(x_117);
x_144 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
lean_inc(x_29);
x_145 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(x_29, x_1, x_117, x_143, x_144, x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec(x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_free_object(x_145);
x_149 = l_Lean_mkAppN(x_111, x_117);
x_150 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_149, x_10);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_152 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_7);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15;
lean_inc_ref(x_1);
x_157 = l_Lean_mkApp4(x_156, x_1, x_155, x_153, x_151);
x_158 = lean_array_get_size(x_117);
x_159 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16;
x_160 = lean_nat_dec_lt(x_139, x_158);
if (x_160 == 0)
{
uint8_t x_161; 
lean_dec(x_117);
x_161 = lean_unbox(x_121);
lean_dec(x_121);
x_71 = x_157;
x_72 = x_161;
x_73 = x_159;
x_74 = lean_box(0);
goto block_101;
}
else
{
uint8_t x_162; 
x_162 = lean_nat_dec_le(x_158, x_158);
if (x_162 == 0)
{
if (x_160 == 0)
{
uint8_t x_163; 
lean_dec(x_117);
x_163 = lean_unbox(x_121);
lean_dec(x_121);
x_71 = x_157;
x_72 = x_163;
x_73 = x_159;
x_74 = lean_box(0);
goto block_101;
}
else
{
size_t x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_usize_of_nat(x_158);
x_165 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_117, x_144, x_164, x_159, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_117);
x_166 = lean_unbox(x_121);
lean_dec(x_121);
x_102 = x_157;
x_103 = x_166;
x_104 = x_165;
goto block_109;
}
}
else
{
size_t x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_usize_of_nat(x_158);
x_168 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_117, x_144, x_167, x_159, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_117);
x_169 = lean_unbox(x_121);
lean_dec(x_121);
x_102 = x_157;
x_103 = x_169;
x_104 = x_168;
goto block_109;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_170 = !lean_is_exclusive(x_154);
if (x_170 == 0)
{
return x_154;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_154, 0);
lean_inc(x_171);
lean_dec(x_154);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_151);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_173 = !lean_is_exclusive(x_152);
if (x_173 == 0)
{
return x_152;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_152, 0);
lean_inc(x_174);
lean_dec(x_152);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; 
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_176 = lean_ctor_get(x_148, 0);
lean_inc(x_176);
lean_dec_ref(x_148);
lean_ctor_set(x_145, 0, x_176);
return x_145;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_145, 0);
lean_inc(x_177);
lean_dec(x_145);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec(x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = l_Lean_mkAppN(x_111, x_117);
x_180 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_179, x_10);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_182 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_7);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15;
lean_inc_ref(x_1);
x_187 = l_Lean_mkApp4(x_186, x_1, x_185, x_183, x_181);
x_188 = lean_array_get_size(x_117);
x_189 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16;
x_190 = lean_nat_dec_lt(x_139, x_188);
if (x_190 == 0)
{
uint8_t x_191; 
lean_dec(x_117);
x_191 = lean_unbox(x_121);
lean_dec(x_121);
x_71 = x_187;
x_72 = x_191;
x_73 = x_189;
x_74 = lean_box(0);
goto block_101;
}
else
{
uint8_t x_192; 
x_192 = lean_nat_dec_le(x_188, x_188);
if (x_192 == 0)
{
if (x_190 == 0)
{
uint8_t x_193; 
lean_dec(x_117);
x_193 = lean_unbox(x_121);
lean_dec(x_121);
x_71 = x_187;
x_72 = x_193;
x_73 = x_189;
x_74 = lean_box(0);
goto block_101;
}
else
{
size_t x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_usize_of_nat(x_188);
x_195 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_117, x_144, x_194, x_189, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_117);
x_196 = lean_unbox(x_121);
lean_dec(x_121);
x_102 = x_187;
x_103 = x_196;
x_104 = x_195;
goto block_109;
}
}
else
{
size_t x_197; lean_object* x_198; uint8_t x_199; 
x_197 = lean_usize_of_nat(x_188);
x_198 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_117, x_144, x_197, x_189, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_117);
x_199 = lean_unbox(x_121);
lean_dec(x_121);
x_102 = x_187;
x_103 = x_199;
x_104 = x_198;
goto block_109;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_183);
lean_dec(x_181);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_200 = lean_ctor_get(x_184, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_201 = x_184;
} else {
 lean_dec_ref(x_184);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 1, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_181);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_203 = lean_ctor_get(x_182, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_204 = x_182;
} else {
 lean_dec_ref(x_182);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 1, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_206 = lean_ctor_get(x_178, 0);
lean_inc(x_206);
lean_dec_ref(x_178);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_208 = !lean_is_exclusive(x_145);
if (x_208 == 0)
{
return x_145;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_145, 0);
lean_inc(x_209);
lean_dec(x_145);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
}
}
else
{
uint8_t x_211; 
lean_free_object(x_115);
lean_dec(x_119);
lean_dec(x_118);
lean_free_object(x_112);
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_211 = !lean_is_exclusive(x_120);
if (x_211 == 0)
{
return x_120;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_120, 0);
lean_inc(x_212);
lean_dec(x_120);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_112, 0);
x_215 = lean_ctor_get(x_115, 0);
x_216 = lean_ctor_get(x_115, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_115);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_216);
lean_inc_ref(x_1);
x_217 = l_Lean_Meta_isExprDefEq(x_1, x_216, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
x_219 = lean_unbox(x_218);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec(x_218);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_111);
lean_dec(x_3);
x_220 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_ctor_get_uint8(x_221, sizeof(void*)*11 + 14);
lean_dec(x_221);
if (x_222 == 0)
{
lean_dec(x_216);
lean_free_object(x_112);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_223 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1;
x_224 = l_Lean_MessageData_ofName(x_29);
x_225 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
lean_ctor_set_tag(x_112, 7);
lean_ctor_set(x_112, 1, x_226);
lean_ctor_set(x_112, 0, x_225);
x_227 = l_Lean_indentExpr(x_1);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_112);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10;
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Lean_indentExpr(x_216);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_Meta_Grind_reportIssue(x_232, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_233) == 0)
{
lean_dec_ref(x_233);
x_14 = lean_box(0);
goto block_17;
}
else
{
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_216);
lean_free_object(x_112);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_234 = lean_ctor_get(x_220, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_235 = x_220;
} else {
 lean_dec_ref(x_220);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_234);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; size_t x_242; size_t x_243; lean_object* x_244; 
lean_dec(x_216);
lean_free_object(x_112);
x_237 = lean_unsigned_to_nat(0u);
x_238 = lean_array_get_size(x_215);
x_239 = l_Array_toSubarray___redArg(x_215, x_237, x_238);
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_array_size(x_214);
x_243 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
lean_inc(x_29);
x_244 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(x_29, x_1, x_214, x_242, x_243, x_241, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_dec(x_245);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_246);
x_248 = l_Lean_mkAppN(x_111, x_214);
x_249 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_248, x_10);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_251 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
x_253 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_7);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15;
lean_inc_ref(x_1);
x_256 = l_Lean_mkApp4(x_255, x_1, x_254, x_252, x_250);
x_257 = lean_array_get_size(x_214);
x_258 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16;
x_259 = lean_nat_dec_lt(x_237, x_257);
if (x_259 == 0)
{
uint8_t x_260; 
lean_dec(x_214);
x_260 = lean_unbox(x_218);
lean_dec(x_218);
x_71 = x_256;
x_72 = x_260;
x_73 = x_258;
x_74 = lean_box(0);
goto block_101;
}
else
{
uint8_t x_261; 
x_261 = lean_nat_dec_le(x_257, x_257);
if (x_261 == 0)
{
if (x_259 == 0)
{
uint8_t x_262; 
lean_dec(x_214);
x_262 = lean_unbox(x_218);
lean_dec(x_218);
x_71 = x_256;
x_72 = x_262;
x_73 = x_258;
x_74 = lean_box(0);
goto block_101;
}
else
{
size_t x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_usize_of_nat(x_257);
x_264 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_214, x_243, x_263, x_258, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_214);
x_265 = lean_unbox(x_218);
lean_dec(x_218);
x_102 = x_256;
x_103 = x_265;
x_104 = x_264;
goto block_109;
}
}
else
{
size_t x_266; lean_object* x_267; uint8_t x_268; 
x_266 = lean_usize_of_nat(x_257);
x_267 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_214, x_243, x_266, x_258, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_214);
x_268 = lean_unbox(x_218);
lean_dec(x_218);
x_102 = x_256;
x_103 = x_268;
x_104 = x_267;
goto block_109;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_269 = lean_ctor_get(x_253, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_270 = x_253;
} else {
 lean_dec_ref(x_253);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_250);
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_272 = lean_ctor_get(x_251, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_273 = x_251;
} else {
 lean_dec_ref(x_251);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_275 = lean_ctor_get(x_247, 0);
lean_inc(x_275);
lean_dec_ref(x_247);
if (lean_is_scalar(x_246)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_246;
}
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_244, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_278 = x_244;
} else {
 lean_dec_ref(x_244);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_216);
lean_dec(x_215);
lean_free_object(x_112);
lean_dec(x_214);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_280 = lean_ctor_get(x_217, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_281 = x_217;
} else {
 lean_dec_ref(x_217);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_280);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_283 = lean_ctor_get(x_112, 1);
x_284 = lean_ctor_get(x_112, 0);
lean_inc(x_283);
lean_inc(x_284);
lean_dec(x_112);
x_285 = lean_ctor_get(x_283, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_287 = x_283;
} else {
 lean_dec_ref(x_283);
 x_287 = lean_box(0);
}
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_286);
lean_inc_ref(x_1);
x_288 = l_Lean_Meta_isExprDefEq(x_1, x_286, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
x_290 = lean_unbox(x_289);
if (x_290 == 0)
{
lean_object* x_291; 
lean_dec(x_289);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_111);
lean_dec(x_3);
x_291 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = lean_ctor_get_uint8(x_292, sizeof(void*)*11 + 14);
lean_dec(x_292);
if (x_293 == 0)
{
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_294 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1;
x_295 = l_Lean_MessageData_ofName(x_29);
if (lean_is_scalar(x_287)) {
 x_296 = lean_alloc_ctor(7, 2, 0);
} else {
 x_296 = x_287;
 lean_ctor_set_tag(x_296, 7);
}
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
x_298 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = l_Lean_indentExpr(x_1);
x_300 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10;
x_302 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Lean_indentExpr(x_286);
x_304 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Meta_Grind_reportIssue(x_304, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_305) == 0)
{
lean_dec_ref(x_305);
x_14 = lean_box(0);
goto block_17;
}
else
{
return x_305;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_306 = lean_ctor_get(x_291, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_307 = x_291;
} else {
 lean_dec_ref(x_291);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_306);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; size_t x_314; size_t x_315; lean_object* x_316; 
lean_dec(x_286);
x_309 = lean_unsigned_to_nat(0u);
x_310 = lean_array_get_size(x_285);
x_311 = l_Array_toSubarray___redArg(x_285, x_309, x_310);
x_312 = lean_box(0);
if (lean_is_scalar(x_287)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_287;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_311);
x_314 = lean_array_size(x_284);
x_315 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
lean_inc(x_29);
x_316 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(x_29, x_1, x_284, x_314, x_315, x_313, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_318 = x_316;
} else {
 lean_dec_ref(x_316);
 x_318 = lean_box(0);
}
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
lean_dec(x_317);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_318);
x_320 = l_Lean_mkAppN(x_111, x_284);
x_321 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_320, x_10);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_dec_ref(x_321);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_323 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
lean_dec_ref(x_323);
x_325 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_7);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
lean_dec_ref(x_325);
x_327 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15;
lean_inc_ref(x_1);
x_328 = l_Lean_mkApp4(x_327, x_1, x_326, x_324, x_322);
x_329 = lean_array_get_size(x_284);
x_330 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16;
x_331 = lean_nat_dec_lt(x_309, x_329);
if (x_331 == 0)
{
uint8_t x_332; 
lean_dec(x_284);
x_332 = lean_unbox(x_289);
lean_dec(x_289);
x_71 = x_328;
x_72 = x_332;
x_73 = x_330;
x_74 = lean_box(0);
goto block_101;
}
else
{
uint8_t x_333; 
x_333 = lean_nat_dec_le(x_329, x_329);
if (x_333 == 0)
{
if (x_331 == 0)
{
uint8_t x_334; 
lean_dec(x_284);
x_334 = lean_unbox(x_289);
lean_dec(x_289);
x_71 = x_328;
x_72 = x_334;
x_73 = x_330;
x_74 = lean_box(0);
goto block_101;
}
else
{
size_t x_335; lean_object* x_336; uint8_t x_337; 
x_335 = lean_usize_of_nat(x_329);
x_336 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_284, x_315, x_335, x_330, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_284);
x_337 = lean_unbox(x_289);
lean_dec(x_289);
x_102 = x_328;
x_103 = x_337;
x_104 = x_336;
goto block_109;
}
}
else
{
size_t x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_usize_of_nat(x_329);
x_339 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_284, x_315, x_338, x_330, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_284);
x_340 = lean_unbox(x_289);
lean_dec(x_289);
x_102 = x_328;
x_103 = x_340;
x_104 = x_339;
goto block_109;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_289);
lean_dec(x_284);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_341 = lean_ctor_get(x_325, 0);
lean_inc(x_341);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_342 = x_325;
} else {
 lean_dec_ref(x_325);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_341);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_322);
lean_dec(x_289);
lean_dec(x_284);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_344 = lean_ctor_get(x_323, 0);
lean_inc(x_344);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 x_345 = x_323;
} else {
 lean_dec_ref(x_323);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 1, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_344);
return x_346;
}
}
else
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_289);
lean_dec(x_284);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_347 = lean_ctor_get(x_319, 0);
lean_inc(x_347);
lean_dec_ref(x_319);
if (lean_is_scalar(x_318)) {
 x_348 = lean_alloc_ctor(0, 1, 0);
} else {
 x_348 = x_318;
}
lean_ctor_set(x_348, 0, x_347);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_289);
lean_dec(x_284);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_349 = lean_ctor_get(x_316, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_350 = x_316;
} else {
 lean_dec_ref(x_316);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 1, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_349);
return x_351;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_111);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_352 = lean_ctor_get(x_288, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_353 = x_288;
} else {
 lean_dec_ref(x_288);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 1, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_352);
return x_354;
}
}
}
}
else
{
uint8_t x_436; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_436 = !lean_is_exclusive(x_110);
if (x_436 == 0)
{
return x_110;
}
else
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_110, 0);
lean_inc(x_437);
lean_dec(x_110);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
return x_438;
}
}
block_47:
{
lean_object* x_31; 
x_31 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*11 + 14);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1;
x_35 = l_Lean_MessageData_ofName(x_29);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_indentExpr(x_1);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__3;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_Grind_reportIssue(x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
x_18 = lean_box(0);
goto block_21;
}
else
{
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_31, 0);
lean_inc(x_45);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
block_70:
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_50);
lean_dec_ref(x_1);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_62, x_63);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_29);
x_66 = l_Lean_Meta_Grind_addNewRawFact(x_49, x_48, x_64, x_65, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec(x_50);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_29);
x_67 = !lean_is_exclusive(x_61);
if (x_67 == 0)
{
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
block_101:
{
uint8_t x_75; uint8_t x_76; lean_object* x_77; 
x_75 = 0;
x_76 = 1;
x_77 = l_Lean_Meta_mkLambdaFVars(x_73, x_71, x_75, x_72, x_75, x_72, x_76, x_9, x_10, x_11, x_12);
lean_dec_ref(x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_78, x_10);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_80);
x_81 = lean_infer_type(x_80, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l_Lean_Expr_hasMVar(x_80);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = l_Lean_Expr_hasMVar(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__6));
x_86 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(x_85, x_11);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
x_48 = x_82;
x_49 = x_80;
x_50 = x_3;
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
x_59 = x_12;
x_60 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_inc(x_29);
x_89 = l_Lean_MessageData_ofName(x_29);
x_90 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__8;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_82);
x_92 = l_Lean_MessageData_ofExpr(x_82);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(x_85, x_93, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_94) == 0)
{
lean_dec_ref(x_94);
x_48 = x_82;
x_49 = x_80;
x_50 = x_3;
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
x_59 = x_12;
x_60 = lean_box(0);
goto block_70;
}
else
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_94;
}
}
}
else
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_3);
x_30 = lean_box(0);
goto block_47;
}
}
else
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_3);
x_30 = lean_box(0);
goto block_47;
}
}
else
{
uint8_t x_95; 
lean_dec(x_80);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_81);
if (x_95 == 0)
{
return x_81;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_81, 0);
lean_inc(x_96);
lean_dec(x_81);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_98 = !lean_is_exclusive(x_77);
if (x_98 == 0)
{
return x_77;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_77, 0);
lean_inc(x_99);
lean_dec(x_77);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
block_109:
{
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_71 = x_102;
x_72 = x_103;
x_73 = x_105;
x_74 = lean_box(0);
goto block_101;
}
else
{
uint8_t x_106; 
lean_dec_ref(x_102);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
return x_104;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
}
}
else
{
lean_object* x_439; uint8_t x_440; 
x_439 = lean_ctor_get(x_24, 0);
lean_inc(x_439);
lean_dec(x_24);
x_440 = lean_nat_dec_lt(x_23, x_439);
lean_dec(x_439);
lean_dec(x_23);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_441 = lean_box(0);
x_442 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_442, 0, x_441);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_516; uint8_t x_517; lean_object* x_518; lean_object* x_524; 
x_443 = lean_ctor_get(x_2, 0);
lean_inc(x_443);
lean_dec_ref(x_2);
lean_inc_ref(x_11);
lean_inc(x_443);
x_524 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_443, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_602; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
lean_dec_ref(x_524);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_525);
x_602 = lean_infer_type(x_525, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; uint8_t x_605; uint8_t x_606; uint8_t x_607; uint8_t x_608; uint8_t x_609; uint8_t x_610; uint8_t x_611; uint8_t x_612; uint8_t x_613; uint8_t x_614; uint8_t x_615; uint8_t x_616; uint8_t x_617; uint8_t x_618; uint8_t x_619; uint8_t x_620; uint8_t x_621; uint8_t x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_632; uint8_t x_633; uint8_t x_634; lean_object* x_635; uint64_t x_636; uint64_t x_637; uint64_t x_638; lean_object* x_639; uint8_t x_640; uint64_t x_641; uint64_t x_642; uint64_t x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
lean_dec_ref(x_602);
x_604 = l_Lean_Meta_Context_config(x_9);
x_605 = lean_ctor_get_uint8(x_604, 0);
x_606 = lean_ctor_get_uint8(x_604, 1);
x_607 = lean_ctor_get_uint8(x_604, 2);
x_608 = lean_ctor_get_uint8(x_604, 3);
x_609 = lean_ctor_get_uint8(x_604, 4);
x_610 = lean_ctor_get_uint8(x_604, 5);
x_611 = lean_ctor_get_uint8(x_604, 6);
x_612 = lean_ctor_get_uint8(x_604, 7);
x_613 = lean_ctor_get_uint8(x_604, 8);
x_614 = lean_ctor_get_uint8(x_604, 10);
x_615 = lean_ctor_get_uint8(x_604, 11);
x_616 = lean_ctor_get_uint8(x_604, 12);
x_617 = lean_ctor_get_uint8(x_604, 13);
x_618 = lean_ctor_get_uint8(x_604, 14);
x_619 = lean_ctor_get_uint8(x_604, 15);
x_620 = lean_ctor_get_uint8(x_604, 16);
x_621 = lean_ctor_get_uint8(x_604, 17);
x_622 = lean_ctor_get_uint8(x_604, 18);
if (lean_is_exclusive(x_604)) {
 x_623 = x_604;
} else {
 lean_dec_ref(x_604);
 x_623 = lean_box(0);
}
x_624 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
x_625 = lean_ctor_get(x_9, 1);
x_626 = lean_ctor_get(x_9, 2);
x_627 = lean_ctor_get(x_9, 3);
x_628 = lean_ctor_get(x_9, 4);
x_629 = lean_ctor_get(x_9, 5);
x_630 = lean_ctor_get(x_9, 6);
x_631 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 1);
x_632 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 2);
x_633 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 3);
x_634 = 1;
if (lean_is_scalar(x_623)) {
 x_635 = lean_alloc_ctor(0, 0, 19);
} else {
 x_635 = x_623;
}
lean_ctor_set_uint8(x_635, 0, x_605);
lean_ctor_set_uint8(x_635, 1, x_606);
lean_ctor_set_uint8(x_635, 2, x_607);
lean_ctor_set_uint8(x_635, 3, x_608);
lean_ctor_set_uint8(x_635, 4, x_609);
lean_ctor_set_uint8(x_635, 5, x_610);
lean_ctor_set_uint8(x_635, 6, x_611);
lean_ctor_set_uint8(x_635, 7, x_612);
lean_ctor_set_uint8(x_635, 8, x_613);
lean_ctor_set_uint8(x_635, 9, x_634);
lean_ctor_set_uint8(x_635, 10, x_614);
lean_ctor_set_uint8(x_635, 11, x_615);
lean_ctor_set_uint8(x_635, 12, x_616);
lean_ctor_set_uint8(x_635, 13, x_617);
lean_ctor_set_uint8(x_635, 14, x_618);
lean_ctor_set_uint8(x_635, 15, x_619);
lean_ctor_set_uint8(x_635, 16, x_620);
lean_ctor_set_uint8(x_635, 17, x_621);
lean_ctor_set_uint8(x_635, 18, x_622);
x_636 = l_Lean_Meta_Context_configKey(x_9);
x_637 = 2;
x_638 = lean_uint64_shift_right(x_636, x_637);
x_639 = lean_box(0);
x_640 = 0;
x_641 = lean_uint64_shift_left(x_638, x_637);
x_642 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__17;
x_643 = lean_uint64_lor(x_641, x_642);
x_644 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_644, 0, x_635);
lean_ctor_set_uint64(x_644, sizeof(void*)*1, x_643);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_628);
lean_inc_ref(x_627);
lean_inc_ref(x_626);
lean_inc(x_625);
x_645 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_625);
lean_ctor_set(x_645, 2, x_626);
lean_ctor_set(x_645, 3, x_627);
lean_ctor_set(x_645, 4, x_628);
lean_ctor_set(x_645, 5, x_629);
lean_ctor_set(x_645, 6, x_630);
lean_ctor_set_uint8(x_645, sizeof(void*)*7, x_624);
lean_ctor_set_uint8(x_645, sizeof(void*)*7 + 1, x_631);
lean_ctor_set_uint8(x_645, sizeof(void*)*7 + 2, x_632);
lean_ctor_set_uint8(x_645, sizeof(void*)*7 + 3, x_633);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
x_646 = l_Lean_Meta_forallMetaTelescopeReducing(x_603, x_639, x_640, x_645, x_10, x_11, x_12);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
lean_dec_ref(x_646);
x_526 = x_647;
x_527 = lean_box(0);
goto block_601;
}
else
{
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_648; 
x_648 = lean_ctor_get(x_646, 0);
lean_inc(x_648);
lean_dec_ref(x_646);
x_526 = x_648;
x_527 = lean_box(0);
goto block_601;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_525);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_649 = lean_ctor_get(x_646, 0);
lean_inc(x_649);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 x_650 = x_646;
} else {
 lean_dec_ref(x_646);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 1, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_649);
return x_651;
}
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_dec(x_525);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_652 = lean_ctor_get(x_602, 0);
lean_inc(x_652);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 x_653 = x_602;
} else {
 lean_dec_ref(x_602);
 x_653 = lean_box(0);
}
if (lean_is_scalar(x_653)) {
 x_654 = lean_alloc_ctor(1, 1, 0);
} else {
 x_654 = x_653;
}
lean_ctor_set(x_654, 0, x_652);
return x_654;
}
block_601:
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_526, 0);
lean_inc(x_529);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_530 = x_526;
} else {
 lean_dec_ref(x_526);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_528, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_528, 1);
lean_inc(x_532);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_533 = x_528;
} else {
 lean_dec_ref(x_528);
 x_533 = lean_box(0);
}
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_532);
lean_inc_ref(x_1);
x_534 = l_Lean_Meta_isExprDefEq(x_1, x_532, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; uint8_t x_536; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
lean_dec_ref(x_534);
x_536 = lean_unbox(x_535);
if (x_536 == 0)
{
lean_object* x_537; 
lean_dec(x_535);
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_525);
lean_dec(x_3);
x_537 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; uint8_t x_539; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
lean_dec_ref(x_537);
x_539 = lean_ctor_get_uint8(x_538, sizeof(void*)*11 + 14);
lean_dec(x_538);
if (x_539 == 0)
{
lean_dec(x_533);
lean_dec(x_532);
lean_dec(x_530);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_540 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1;
x_541 = l_Lean_MessageData_ofName(x_443);
if (lean_is_scalar(x_533)) {
 x_542 = lean_alloc_ctor(7, 2, 0);
} else {
 x_542 = x_533;
 lean_ctor_set_tag(x_542, 7);
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_541);
x_543 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
if (lean_is_scalar(x_530)) {
 x_544 = lean_alloc_ctor(7, 2, 0);
} else {
 x_544 = x_530;
 lean_ctor_set_tag(x_544, 7);
}
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
x_545 = l_Lean_indentExpr(x_1);
x_546 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
x_547 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10;
x_548 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
x_549 = l_Lean_indentExpr(x_532);
x_550 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
x_551 = l_Lean_Meta_Grind_reportIssue(x_550, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_551) == 0)
{
lean_dec_ref(x_551);
x_14 = lean_box(0);
goto block_17;
}
else
{
return x_551;
}
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_533);
lean_dec(x_532);
lean_dec(x_530);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_552 = lean_ctor_get(x_537, 0);
lean_inc(x_552);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 x_553 = x_537;
} else {
 lean_dec_ref(x_537);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(1, 1, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_552);
return x_554;
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; size_t x_560; size_t x_561; lean_object* x_562; 
lean_dec(x_532);
lean_dec(x_530);
x_555 = lean_unsigned_to_nat(0u);
x_556 = lean_array_get_size(x_531);
x_557 = l_Array_toSubarray___redArg(x_531, x_555, x_556);
x_558 = lean_box(0);
if (lean_is_scalar(x_533)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_533;
}
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_557);
x_560 = lean_array_size(x_529);
x_561 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
lean_inc(x_443);
x_562 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(x_443, x_1, x_529, x_560, x_561, x_559, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 x_564 = x_562;
} else {
 lean_dec_ref(x_562);
 x_564 = lean_box(0);
}
x_565 = lean_ctor_get(x_563, 0);
lean_inc(x_565);
lean_dec(x_563);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_564);
x_566 = l_Lean_mkAppN(x_525, x_529);
x_567 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_566, x_10);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
lean_dec_ref(x_567);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_569 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
lean_dec_ref(x_569);
x_571 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_7);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
x_573 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15;
lean_inc_ref(x_1);
x_574 = l_Lean_mkApp4(x_573, x_1, x_572, x_570, x_568);
x_575 = lean_array_get_size(x_529);
x_576 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16;
x_577 = lean_nat_dec_lt(x_555, x_575);
if (x_577 == 0)
{
uint8_t x_578; 
lean_dec(x_529);
x_578 = lean_unbox(x_535);
lean_dec(x_535);
x_485 = x_574;
x_486 = x_578;
x_487 = x_576;
x_488 = lean_box(0);
goto block_515;
}
else
{
uint8_t x_579; 
x_579 = lean_nat_dec_le(x_575, x_575);
if (x_579 == 0)
{
if (x_577 == 0)
{
uint8_t x_580; 
lean_dec(x_529);
x_580 = lean_unbox(x_535);
lean_dec(x_535);
x_485 = x_574;
x_486 = x_580;
x_487 = x_576;
x_488 = lean_box(0);
goto block_515;
}
else
{
size_t x_581; lean_object* x_582; uint8_t x_583; 
x_581 = lean_usize_of_nat(x_575);
x_582 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_529, x_561, x_581, x_576, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_529);
x_583 = lean_unbox(x_535);
lean_dec(x_535);
x_516 = x_574;
x_517 = x_583;
x_518 = x_582;
goto block_523;
}
}
else
{
size_t x_584; lean_object* x_585; uint8_t x_586; 
x_584 = lean_usize_of_nat(x_575);
x_585 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(x_529, x_561, x_584, x_576, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_529);
x_586 = lean_unbox(x_535);
lean_dec(x_535);
x_516 = x_574;
x_517 = x_586;
x_518 = x_585;
goto block_523;
}
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_535);
lean_dec(x_529);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_587 = lean_ctor_get(x_571, 0);
lean_inc(x_587);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 x_588 = x_571;
} else {
 lean_dec_ref(x_571);
 x_588 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_589 = lean_alloc_ctor(1, 1, 0);
} else {
 x_589 = x_588;
}
lean_ctor_set(x_589, 0, x_587);
return x_589;
}
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_568);
lean_dec(x_535);
lean_dec(x_529);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_590 = lean_ctor_get(x_569, 0);
lean_inc(x_590);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 x_591 = x_569;
} else {
 lean_dec_ref(x_569);
 x_591 = lean_box(0);
}
if (lean_is_scalar(x_591)) {
 x_592 = lean_alloc_ctor(1, 1, 0);
} else {
 x_592 = x_591;
}
lean_ctor_set(x_592, 0, x_590);
return x_592;
}
}
else
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_535);
lean_dec(x_529);
lean_dec(x_525);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_593 = lean_ctor_get(x_565, 0);
lean_inc(x_593);
lean_dec_ref(x_565);
if (lean_is_scalar(x_564)) {
 x_594 = lean_alloc_ctor(0, 1, 0);
} else {
 x_594 = x_564;
}
lean_ctor_set(x_594, 0, x_593);
return x_594;
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_535);
lean_dec(x_529);
lean_dec(x_525);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_595 = lean_ctor_get(x_562, 0);
lean_inc(x_595);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 x_596 = x_562;
} else {
 lean_dec_ref(x_562);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 1, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_595);
return x_597;
}
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_533);
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_525);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_598 = lean_ctor_get(x_534, 0);
lean_inc(x_598);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 x_599 = x_534;
} else {
 lean_dec_ref(x_534);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 1, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_598);
return x_600;
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_655 = lean_ctor_get(x_524, 0);
lean_inc(x_655);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 x_656 = x_524;
} else {
 lean_dec_ref(x_524);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(1, 1, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_655);
return x_657;
}
block_461:
{
lean_object* x_445; 
x_445 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; uint8_t x_447; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
lean_dec_ref(x_445);
x_447 = lean_ctor_get_uint8(x_446, sizeof(void*)*11 + 14);
lean_dec(x_446);
if (x_447 == 0)
{
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_448 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1;
x_449 = l_Lean_MessageData_ofName(x_443);
x_450 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_451 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4;
x_452 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
x_453 = l_Lean_indentExpr(x_1);
x_454 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__3;
x_456 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
x_457 = l_Lean_Meta_Grind_reportIssue(x_456, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_457) == 0)
{
lean_dec_ref(x_457);
x_18 = lean_box(0);
goto block_21;
}
else
{
return x_457;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_458 = lean_ctor_get(x_445, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_459 = x_445;
} else {
 lean_dec_ref(x_445);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 1, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_458);
return x_460;
}
}
block_484:
{
lean_object* x_475; 
x_475 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_464);
lean_dec_ref(x_1);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
lean_dec_ref(x_475);
x_477 = lean_unsigned_to_nat(1u);
x_478 = lean_nat_add(x_476, x_477);
lean_dec(x_476);
x_479 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_479, 0, x_443);
x_480 = l_Lean_Meta_Grind_addNewRawFact(x_463, x_462, x_478, x_479, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
return x_480;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec_ref(x_463);
lean_dec_ref(x_462);
lean_dec(x_443);
x_481 = lean_ctor_get(x_475, 0);
lean_inc(x_481);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 x_482 = x_475;
} else {
 lean_dec_ref(x_475);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 1, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_481);
return x_483;
}
}
block_515:
{
uint8_t x_489; uint8_t x_490; lean_object* x_491; 
x_489 = 0;
x_490 = 1;
x_491 = l_Lean_Meta_mkLambdaFVars(x_487, x_485, x_489, x_486, x_489, x_486, x_490, x_9, x_10, x_11, x_12);
lean_dec_ref(x_487);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
lean_dec_ref(x_491);
x_493 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___redArg(x_492, x_10);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
lean_dec_ref(x_493);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_494);
x_495 = lean_infer_type(x_494, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; uint8_t x_497; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
lean_dec_ref(x_495);
x_497 = l_Lean_Expr_hasMVar(x_494);
if (x_497 == 0)
{
uint8_t x_498; 
x_498 = l_Lean_Expr_hasMVar(x_496);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_499 = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__6));
x_500 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(x_499, x_11);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
lean_dec_ref(x_500);
x_502 = lean_unbox(x_501);
lean_dec(x_501);
if (x_502 == 0)
{
x_462 = x_496;
x_463 = x_494;
x_464 = x_3;
x_465 = x_4;
x_466 = x_5;
x_467 = x_6;
x_468 = x_7;
x_469 = x_8;
x_470 = x_9;
x_471 = x_10;
x_472 = x_11;
x_473 = x_12;
x_474 = lean_box(0);
goto block_484;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_inc(x_443);
x_503 = l_Lean_MessageData_ofName(x_443);
x_504 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__8;
x_505 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
lean_inc(x_496);
x_506 = l_Lean_MessageData_ofExpr(x_496);
x_507 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_506);
x_508 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(x_499, x_507, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_508) == 0)
{
lean_dec_ref(x_508);
x_462 = x_496;
x_463 = x_494;
x_464 = x_3;
x_465 = x_4;
x_466 = x_5;
x_467 = x_6;
x_468 = x_7;
x_469 = x_8;
x_470 = x_9;
x_471 = x_10;
x_472 = x_11;
x_473 = x_12;
x_474 = lean_box(0);
goto block_484;
}
else
{
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_508;
}
}
}
else
{
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_3);
x_444 = lean_box(0);
goto block_461;
}
}
else
{
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_3);
x_444 = lean_box(0);
goto block_461;
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_494);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_509 = lean_ctor_get(x_495, 0);
lean_inc(x_509);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_510 = x_495;
} else {
 lean_dec_ref(x_495);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 1, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_509);
return x_511;
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_512 = lean_ctor_get(x_491, 0);
lean_inc(x_512);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 x_513 = x_491;
} else {
 lean_dec_ref(x_491);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 1, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_512);
return x_514;
}
}
block_523:
{
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
lean_dec_ref(x_518);
x_485 = x_516;
x_486 = x_517;
x_487 = x_519;
x_488 = lean_box(0);
goto block_515;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec_ref(x_516);
lean_dec(x_443);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_520 = lean_ctor_get(x_518, 0);
lean_inc(x_520);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 x_521 = x_518;
} else {
 lean_dec_ref(x_518);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(1, 1, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_520);
return x_522;
}
}
}
}
}
else
{
uint8_t x_658; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_658 = !lean_is_exclusive(x_24);
if (x_658 == 0)
{
return x_24;
}
else
{
lean_object* x_659; lean_object* x_660; 
x_659 = lean_ctor_get(x_24, 0);
lean_inc(x_659);
lean_dec(x_24);
x_660 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_660, 0, x_659);
return x_660;
}
}
}
else
{
uint8_t x_661; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_661 = !lean_is_exclusive(x_22);
if (x_661 == 0)
{
return x_22;
}
else
{
lean_object* x_662; lean_object* x_663; 
x_662 = lean_ctor_get(x_22, 0);
lean_inc(x_662);
lean_dec(x_22);
x_663 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_663, 0, x_662);
return x_663;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed), 13, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
x_15 = 0;
x_16 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_instantiateExtTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(x_1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1();
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___closed__4);
l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0();
l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2);
l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1 = _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__1);
l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__3 = _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__3);
l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__8 = _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__8);
l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10 = _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__10);
l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15 = _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__15);
l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16 = _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__16);
l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__17 = _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___closed__17();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
