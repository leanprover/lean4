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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getMaxGeneration___redArg(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_synthInstanceAndAssign___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "failed to synthesize instance when instantiating extensionality theorem `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(189, 159, 161, 247, 89, 7, 26, 174)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to apply extensionality theorem `"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\nresulting terms contain metavariables"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\nis not definitionally equal to"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16;
static const lean_array_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_e_30_, v___y_38_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___boxed(lean_object* v_e_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(v_e_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec(v___y_44_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object* v_cls_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_options_62_; uint8_t v_hasTrace_63_; 
v_options_62_ = lean_ctor_get(v___y_60_, 2);
v_hasTrace_63_ = lean_ctor_get_uint8(v_options_62_, sizeof(void*)*1);
if (v_hasTrace_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_cls_59_);
v___x_64_ = lean_box(v_hasTrace_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
else
{
lean_object* v_inheritedTraceOptions_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_inheritedTraceOptions_66_ = lean_ctor_get(v___y_60_, 13);
v___x_67_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
v___x_68_ = l_Lean_Name_append(v___x_67_, v_cls_59_);
v___x_69_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_66_, v_options_62_, v___x_68_);
lean_dec(v___x_68_);
v___x_70_ = lean_box(v___x_69_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object* v_cls_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_72_, v___y_73_);
lean_dec_ref(v___y_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object* v_cls_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_76_, v___y_85_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object* v_cls_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(v_cls_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec(v___y_90_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg___lam__0(lean_object* v_k_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_apply_11(v_k_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, lean_box(0));
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg___lam__0___boxed(lean_object* v_k_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg___lam__0(v_k_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg(lean_object* v_k_128_, uint8_t v_allowLevelAssignments_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; 
v___f_141_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_141_, 0, v_k_128_);
lean_closure_set(v___f_141_, 1, v___y_130_);
lean_closure_set(v___f_141_, 2, v___y_131_);
lean_closure_set(v___f_141_, 3, v___y_132_);
lean_closure_set(v___f_141_, 4, v___y_133_);
lean_closure_set(v___f_141_, 5, v___y_134_);
lean_closure_set(v___f_141_, 6, v___y_135_);
v___x_142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_129_, v___f_141_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_142_) == 0)
{
return v___x_142_;
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg___boxed(lean_object* v_k_151_, lean_object* v_allowLevelAssignments_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_164_; lean_object* v_res_165_; 
v_allowLevelAssignments_boxed_164_ = lean_unbox(v_allowLevelAssignments_152_);
v_res_165_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg(v_k_151_, v_allowLevelAssignments_boxed_164_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7(lean_object* v_00_u03b1_166_, lean_object* v_k_167_, uint8_t v_allowLevelAssignments_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg(v_k_167_, v_allowLevelAssignments_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___boxed(lean_object* v_00_u03b1_181_, lean_object* v_k_182_, lean_object* v_allowLevelAssignments_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_195_; lean_object* v_res_196_; 
v_allowLevelAssignments_boxed_195_ = lean_unbox(v_allowLevelAssignments_183_);
v_res_196_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7(v_00_u03b1_181_, v_k_182_, v_allowLevelAssignments_boxed_195_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_ks_201_; lean_object* v_vs_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_226_; 
v_ks_201_ = lean_ctor_get(v_x_197_, 0);
v_vs_202_ = lean_ctor_get(v_x_197_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_197_);
if (v_isSharedCheck_226_ == 0)
{
v___x_204_ = v_x_197_;
v_isShared_205_ = v_isSharedCheck_226_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_vs_202_);
lean_inc(v_ks_201_);
lean_dec(v_x_197_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_226_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_array_get_size(v_ks_201_);
v___x_207_ = lean_nat_dec_lt(v_x_198_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
lean_dec(v_x_198_);
v___x_208_ = lean_array_push(v_ks_201_, v_x_199_);
v___x_209_ = lean_array_push(v_vs_202_, v_x_200_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_209_);
lean_ctor_set(v___x_204_, 0, v___x_208_);
v___x_211_ = v___x_204_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
else
{
lean_object* v_k_x27_213_; uint8_t v___x_214_; 
v_k_x27_213_ = lean_array_fget_borrowed(v_ks_201_, v_x_198_);
v___x_214_ = l_Lean_instBEqMVarId_beq(v_x_199_, v_k_x27_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_216_; 
if (v_isShared_205_ == 0)
{
v___x_216_ = v___x_204_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_ks_201_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_vs_202_);
v___x_216_ = v_reuseFailAlloc_220_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_add(v_x_198_, v___x_217_);
lean_dec(v_x_198_);
v_x_197_ = v___x_216_;
v_x_198_ = v___x_218_;
goto _start;
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = lean_array_fset(v_ks_201_, v_x_198_, v_x_199_);
v___x_222_ = lean_array_fset(v_vs_202_, v_x_198_, v_x_200_);
lean_dec(v_x_198_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_222_);
lean_ctor_set(v___x_204_, 0, v___x_221_);
v___x_224_ = v___x_204_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_n_227_, lean_object* v_k_228_, lean_object* v_v_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_n_227_, v___x_230_, v_k_228_, v_v_229_);
return v___x_231_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; 
v___x_232_ = ((size_t)5ULL);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_shift_left(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; 
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__0);
v___x_237_ = lean_usize_sub(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(lean_object* v_x_239_, size_t v_x_240_, size_t v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_object* v_es_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v_j_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_es_244_ = lean_ctor_get(v_x_239_, 0);
v___x_245_ = ((size_t)5ULL);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_248_ = lean_usize_land(v_x_240_, v___x_247_);
v_j_249_ = lean_usize_to_nat(v___x_248_);
v___x_250_ = lean_array_get_size(v_es_244_);
v___x_251_ = lean_nat_dec_lt(v_j_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v_j_249_);
lean_dec(v_x_243_);
lean_dec(v_x_242_);
return v_x_239_;
}
else
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_288_; 
lean_inc_ref(v_es_244_);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_239_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v_x_239_, 0);
lean_dec(v_unused_289_);
v___x_253_ = v_x_239_;
v_isShared_254_ = v_isSharedCheck_288_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_x_239_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_288_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_v_255_; lean_object* v___x_256_; lean_object* v_xs_x27_257_; lean_object* v___y_259_; 
v_v_255_ = lean_array_fget(v_es_244_, v_j_249_);
v___x_256_ = lean_box(0);
v_xs_x27_257_ = lean_array_fset(v_es_244_, v_j_249_, v___x_256_);
switch(lean_obj_tag(v_v_255_))
{
case 0:
{
lean_object* v_key_264_; lean_object* v_val_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_275_; 
v_key_264_ = lean_ctor_get(v_v_255_, 0);
v_val_265_ = lean_ctor_get(v_v_255_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_v_255_);
if (v_isSharedCheck_275_ == 0)
{
v___x_267_ = v_v_255_;
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_val_265_);
lean_inc(v_key_264_);
lean_dec(v_v_255_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
uint8_t v___x_269_; 
v___x_269_ = l_Lean_instBEqMVarId_beq(v_x_242_, v_key_264_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_del_object(v___x_267_);
v___x_270_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_264_, v_val_265_, v_x_242_, v_x_243_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___y_259_ = v___x_271_;
goto v___jp_258_;
}
else
{
lean_object* v___x_273_; 
lean_dec(v_val_265_);
lean_dec(v_key_264_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_x_243_);
lean_ctor_set(v___x_267_, 0, v_x_242_);
v___x_273_ = v___x_267_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_x_242_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_x_243_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
v___y_259_ = v___x_273_;
goto v___jp_258_;
}
}
}
}
case 1:
{
lean_object* v_node_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_286_; 
v_node_276_ = lean_ctor_get(v_v_255_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_v_255_);
if (v_isSharedCheck_286_ == 0)
{
v___x_278_ = v_v_255_;
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_node_276_);
lean_dec(v_v_255_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_280_ = lean_usize_shift_right(v_x_240_, v___x_245_);
v___x_281_ = lean_usize_add(v_x_241_, v___x_246_);
v___x_282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(v_node_276_, v___x_280_, v___x_281_, v_x_242_, v_x_243_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_282_);
v___x_284_ = v___x_278_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
v___y_259_ = v___x_284_;
goto v___jp_258_;
}
}
}
default: 
{
lean_object* v___x_287_; 
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v_x_242_);
lean_ctor_set(v___x_287_, 1, v_x_243_);
v___y_259_ = v___x_287_;
goto v___jp_258_;
}
}
v___jp_258_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = lean_array_fset(v_xs_x27_257_, v_j_249_, v___y_259_);
lean_dec(v_j_249_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_260_);
v___x_262_ = v___x_253_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
else
{
lean_object* v_ks_290_; lean_object* v_vs_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_311_; 
v_ks_290_ = lean_ctor_get(v_x_239_, 0);
v_vs_291_ = lean_ctor_get(v_x_239_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_239_);
if (v_isSharedCheck_311_ == 0)
{
v___x_293_ = v_x_239_;
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_vs_291_);
lean_inc(v_ks_290_);
lean_dec(v_x_239_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_ks_290_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_vs_291_);
v___x_296_ = v_reuseFailAlloc_310_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v_newNode_297_; uint8_t v___y_299_; size_t v___x_305_; uint8_t v___x_306_; 
v_newNode_297_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10___redArg(v___x_296_, v_x_242_, v_x_243_);
v___x_305_ = ((size_t)7ULL);
v___x_306_ = lean_usize_dec_le(v___x_305_, v_x_241_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_297_);
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
v___y_299_ = v___x_309_;
goto v___jp_298_;
}
else
{
v___y_299_ = v___x_306_;
goto v___jp_298_;
}
v___jp_298_:
{
if (v___y_299_ == 0)
{
lean_object* v_ks_300_; lean_object* v_vs_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_ks_300_ = lean_ctor_get(v_newNode_297_, 0);
lean_inc_ref(v_ks_300_);
v_vs_301_ = lean_ctor_get(v_newNode_297_, 1);
lean_inc_ref(v_vs_301_);
lean_dec_ref(v_newNode_297_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__2);
v___x_304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___redArg(v_x_241_, v_ks_300_, v_vs_301_, v___x_302_, v___x_303_);
lean_dec_ref(v_vs_301_);
lean_dec_ref(v_ks_300_);
return v___x_304_;
}
else
{
return v_newNode_297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___redArg(size_t v_depth_312_, lean_object* v_keys_313_, lean_object* v_vals_314_, lean_object* v_i_315_, lean_object* v_entries_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_keys_313_);
v___x_318_ = lean_nat_dec_lt(v_i_315_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_i_315_);
return v_entries_316_;
}
else
{
lean_object* v_k_319_; lean_object* v_v_320_; uint64_t v___x_321_; size_t v_h_322_; size_t v___x_323_; lean_object* v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v_h_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_k_319_ = lean_array_fget_borrowed(v_keys_313_, v_i_315_);
v_v_320_ = lean_array_fget_borrowed(v_vals_314_, v_i_315_);
v___x_321_ = l_Lean_instHashableMVarId_hash(v_k_319_);
v_h_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_sub(v_depth_312_, v___x_325_);
v___x_327_ = lean_usize_mul(v___x_323_, v___x_326_);
v_h_328_ = lean_usize_shift_right(v_h_322_, v___x_327_);
v___x_329_ = lean_nat_add(v_i_315_, v___x_324_);
lean_dec(v_i_315_);
lean_inc(v_v_320_);
lean_inc(v_k_319_);
v___x_330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(v_entries_316_, v_h_328_, v_depth_312_, v_k_319_, v_v_320_);
v_i_315_ = v___x_329_;
v_entries_316_ = v___x_330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_depth_332_, lean_object* v_keys_333_, lean_object* v_vals_334_, lean_object* v_i_335_, lean_object* v_entries_336_){
_start:
{
size_t v_depth_boxed_337_; lean_object* v_res_338_; 
v_depth_boxed_337_ = lean_unbox_usize(v_depth_332_);
lean_dec(v_depth_332_);
v_res_338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___redArg(v_depth_boxed_337_, v_keys_333_, v_vals_334_, v_i_335_, v_entries_336_);
lean_dec_ref(v_vals_334_);
lean_dec_ref(v_keys_333_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
size_t v_x_233960__boxed_344_; size_t v_x_233961__boxed_345_; lean_object* v_res_346_; 
v_x_233960__boxed_344_ = lean_unbox_usize(v_x_340_);
lean_dec(v_x_340_);
v_x_233961__boxed_345_ = lean_unbox_usize(v_x_341_);
lean_dec(v_x_341_);
v_res_346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(v_x_339_, v_x_233960__boxed_344_, v_x_233961__boxed_345_, v_x_342_, v_x_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
uint64_t v___x_350_; size_t v___x_351_; size_t v___x_352_; lean_object* v___x_353_; 
v___x_350_ = l_Lean_instHashableMVarId_hash(v_x_348_);
v___x_351_ = lean_uint64_to_usize(v___x_350_);
v___x_352_ = ((size_t)1ULL);
v___x_353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(v_x_347_, v___x_351_, v___x_352_, v_x_348_, v_x_349_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object* v_mvarId_354_, lean_object* v_val_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v_mctx_359_; lean_object* v_cache_360_; lean_object* v_zetaDeltaFVarIds_361_; lean_object* v_postponed_362_; lean_object* v_diag_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_390_; 
v___x_358_ = lean_st_ref_take(v___y_356_);
v_mctx_359_ = lean_ctor_get(v___x_358_, 0);
v_cache_360_ = lean_ctor_get(v___x_358_, 1);
v_zetaDeltaFVarIds_361_ = lean_ctor_get(v___x_358_, 2);
v_postponed_362_ = lean_ctor_get(v___x_358_, 3);
v_diag_363_ = lean_ctor_get(v___x_358_, 4);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_390_ == 0)
{
v___x_365_ = v___x_358_;
v_isShared_366_ = v_isSharedCheck_390_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_diag_363_);
lean_inc(v_postponed_362_);
lean_inc(v_zetaDeltaFVarIds_361_);
lean_inc(v_cache_360_);
lean_inc(v_mctx_359_);
lean_dec(v___x_358_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_390_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v_depth_367_; lean_object* v_levelAssignDepth_368_; lean_object* v_mvarCounter_369_; lean_object* v_lDepth_370_; lean_object* v_decls_371_; lean_object* v_userNames_372_; lean_object* v_lAssignment_373_; lean_object* v_eAssignment_374_; lean_object* v_dAssignment_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_389_; 
v_depth_367_ = lean_ctor_get(v_mctx_359_, 0);
v_levelAssignDepth_368_ = lean_ctor_get(v_mctx_359_, 1);
v_mvarCounter_369_ = lean_ctor_get(v_mctx_359_, 2);
v_lDepth_370_ = lean_ctor_get(v_mctx_359_, 3);
v_decls_371_ = lean_ctor_get(v_mctx_359_, 4);
v_userNames_372_ = lean_ctor_get(v_mctx_359_, 5);
v_lAssignment_373_ = lean_ctor_get(v_mctx_359_, 6);
v_eAssignment_374_ = lean_ctor_get(v_mctx_359_, 7);
v_dAssignment_375_ = lean_ctor_get(v_mctx_359_, 8);
v_isSharedCheck_389_ = !lean_is_exclusive(v_mctx_359_);
if (v_isSharedCheck_389_ == 0)
{
v___x_377_ = v_mctx_359_;
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_dAssignment_375_);
lean_inc(v_eAssignment_374_);
lean_inc(v_lAssignment_373_);
lean_inc(v_userNames_372_);
lean_inc(v_decls_371_);
lean_inc(v_lDepth_370_);
lean_inc(v_mvarCounter_369_);
lean_inc(v_levelAssignDepth_368_);
lean_inc(v_depth_367_);
lean_dec(v_mctx_359_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_eAssignment_374_, v_mvarId_354_, v_val_355_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 7, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_depth_367_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_levelAssignDepth_368_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_mvarCounter_369_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_lDepth_370_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_decls_371_);
lean_ctor_set(v_reuseFailAlloc_388_, 5, v_userNames_372_);
lean_ctor_set(v_reuseFailAlloc_388_, 6, v_lAssignment_373_);
lean_ctor_set(v_reuseFailAlloc_388_, 7, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 8, v_dAssignment_375_);
v___x_381_ = v_reuseFailAlloc_388_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_383_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_381_);
v___x_383_ = v___x_365_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_cache_360_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_zetaDeltaFVarIds_361_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v_postponed_362_);
lean_ctor_set(v_reuseFailAlloc_387_, 4, v_diag_363_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_st_ref_set(v___y_356_, v___x_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object* v_mvarId_391_, lean_object* v_val_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_391_, v_val_392_, v___y_393_);
lean_dec(v___y_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(uint8_t v___x_396_, lean_object* v_p_397_, lean_object* v_e_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_Expr_isMVar(v_p_397_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_isExprDefEq(v_p_397_, v_e_398_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec_ref(v___y_405_);
v___x_412_ = l_Lean_Expr_mvarId_x21(v_p_397_);
lean_dec_ref(v_p_397_);
v___x_413_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_412_, v_e_398_, v___y_406_);
lean_dec(v___y_406_);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_413_, 0);
lean_dec(v_unused_422_);
v___x_415_ = v___x_413_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_dec(v___x_413_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_box(v___x_396_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object* v___x_423_, lean_object* v_p_424_, lean_object* v_e_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
uint8_t v___x_234179__boxed_437_; lean_object* v_res_438_; 
v___x_234179__boxed_437_ = lean_unbox(v___x_423_);
v_res_438_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_234179__boxed_437_, v_p_424_, v_e_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec(v___y_426_);
return v_res_438_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___redArg(lean_object* v_keys_439_, lean_object* v_i_440_, lean_object* v_k_441_){
_start:
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_array_get_size(v_keys_439_);
v___x_443_ = lean_nat_dec_lt(v_i_440_, v___x_442_);
if (v___x_443_ == 0)
{
lean_dec(v_i_440_);
return v___x_443_;
}
else
{
lean_object* v_k_x27_444_; uint8_t v___x_445_; 
v_k_x27_444_ = lean_array_fget_borrowed(v_keys_439_, v_i_440_);
v___x_445_ = l_Lean_instBEqMVarId_beq(v_k_441_, v_k_x27_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_i_440_, v___x_446_);
lean_dec(v_i_440_);
v_i_440_ = v___x_447_;
goto _start;
}
else
{
lean_dec(v_i_440_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___redArg___boxed(lean_object* v_keys_449_, lean_object* v_i_450_, lean_object* v_k_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___redArg(v_keys_449_, v_i_450_, v_k_451_);
lean_dec(v_k_451_);
lean_dec_ref(v_keys_449_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___redArg(lean_object* v_x_454_, size_t v_x_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
lean_object* v_es_457_; lean_object* v___x_458_; size_t v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v_j_462_; lean_object* v___x_463_; 
v_es_457_ = lean_ctor_get(v_x_454_, 0);
lean_inc_ref(v_es_457_);
lean_dec_ref(v_x_454_);
v___x_458_ = lean_box(2);
v___x_459_ = ((size_t)5ULL);
v___x_460_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_461_ = lean_usize_land(v_x_455_, v___x_460_);
v_j_462_ = lean_usize_to_nat(v___x_461_);
v___x_463_ = lean_array_get(v___x_458_, v_es_457_, v_j_462_);
lean_dec(v_j_462_);
lean_dec_ref(v_es_457_);
switch(lean_obj_tag(v___x_463_))
{
case 0:
{
lean_object* v_key_464_; uint8_t v___x_465_; 
v_key_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_key_464_);
lean_dec_ref(v___x_463_);
v___x_465_ = l_Lean_instBEqMVarId_beq(v_x_456_, v_key_464_);
lean_dec(v_key_464_);
return v___x_465_;
}
case 1:
{
lean_object* v_node_466_; size_t v___x_467_; 
v_node_466_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_node_466_);
lean_dec_ref(v___x_463_);
v___x_467_ = lean_usize_shift_right(v_x_455_, v___x_459_);
v_x_454_ = v_node_466_;
v_x_455_ = v___x_467_;
goto _start;
}
default: 
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
}
}
else
{
lean_object* v_ks_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_ks_470_ = lean_ctor_get(v_x_454_, 0);
lean_inc_ref(v_ks_470_);
lean_dec_ref(v_x_454_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___redArg(v_ks_470_, v___x_471_, v_x_456_);
lean_dec_ref(v_ks_470_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___redArg___boxed(lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
size_t v_x_234262__boxed_476_; uint8_t v_res_477_; lean_object* v_r_478_; 
v_x_234262__boxed_476_ = lean_unbox_usize(v_x_474_);
lean_dec(v_x_474_);
v_res_477_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___redArg(v_x_473_, v_x_234262__boxed_476_, v_x_475_);
lean_dec(v_x_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
uint64_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v___x_481_ = l_Lean_instHashableMVarId_hash(v_x_480_);
v___x_482_ = lean_uint64_to_usize(v___x_481_);
v___x_483_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___redArg(v_x_479_, v___x_482_, v_x_480_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_484_, v_x_485_);
lean_dec(v_x_485_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object* v_mvarId_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v_mctx_492_; lean_object* v_eAssignment_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_491_ = lean_st_ref_get(v___y_489_);
v_mctx_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_mctx_492_);
lean_dec(v___x_491_);
v_eAssignment_493_ = lean_ctor_get(v_mctx_492_, 7);
lean_inc_ref(v_eAssignment_493_);
lean_dec_ref(v_mctx_492_);
v___x_494_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_493_, v_mvarId_488_);
v___x_495_ = lean_box(v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object* v_mvarId_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec(v_mvarId_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_object* v_as_501_, size_t v_i_502_, size_t v_stop_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_a_517_; uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_eq(v_i_502_, v_stop_503_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_522_ = lean_array_uget_borrowed(v_as_501_, v_i_502_);
v___x_525_ = l_Lean_Expr_mvarId_x21(v___x_522_);
v___x_526_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_525_, v___y_512_);
lean_dec(v___x_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; uint8_t v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = lean_unbox(v_a_527_);
lean_dec(v_a_527_);
if (v___x_528_ == 0)
{
goto v___jp_523_;
}
else
{
v_a_517_ = v_b_504_;
goto v___jp_516_;
}
}
else
{
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_529_; uint8_t v___x_530_; 
v_a_529_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_529_);
lean_dec_ref(v___x_526_);
v___x_530_ = lean_unbox(v_a_529_);
lean_dec(v_a_529_);
if (v___x_530_ == 0)
{
v_a_517_ = v_b_504_;
goto v___jp_516_;
}
else
{
goto v___jp_523_;
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_b_504_);
v_a_531_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_526_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
v___jp_523_:
{
lean_object* v___x_524_; 
lean_inc(v___x_522_);
v___x_524_ = lean_array_push(v_b_504_, v___x_522_);
v_a_517_ = v___x_524_;
goto v___jp_516_;
}
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v_b_504_);
return v___x_539_;
}
v___jp_516_:
{
size_t v___x_518_; size_t v___x_519_; 
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_502_, v___x_518_);
v_i_502_ = v___x_519_;
v_b_504_ = v_a_517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(lean_object* v_as_540_, lean_object* v_i_541_, lean_object* v_stop_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
size_t v_i_boxed_555_; size_t v_stop_boxed_556_; lean_object* v_res_557_; 
v_i_boxed_555_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_stop_boxed_556_ = lean_unbox_usize(v_stop_542_);
lean_dec(v_stop_542_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(v_as_540_, v_i_boxed_555_, v_stop_boxed_556_, v_b_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v_as_540_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5_spec__7(lean_object* v_msgData_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; lean_object* v_env_565_; lean_object* v___x_566_; lean_object* v_mctx_567_; lean_object* v_lctx_568_; lean_object* v_options_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_564_ = lean_st_ref_get(v___y_562_);
v_env_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_env_565_);
lean_dec(v___x_564_);
v___x_566_ = lean_st_ref_get(v___y_560_);
v_mctx_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref(v_mctx_567_);
lean_dec(v___x_566_);
v_lctx_568_ = lean_ctor_get(v___y_559_, 2);
v_options_569_ = lean_ctor_get(v___y_561_, 2);
lean_inc_ref(v_options_569_);
lean_inc_ref(v_lctx_568_);
v___x_570_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_570_, 0, v_env_565_);
lean_ctor_set(v___x_570_, 1, v_mctx_567_);
lean_ctor_set(v___x_570_, 2, v_lctx_568_);
lean_ctor_set(v___x_570_, 3, v_options_569_);
v___x_571_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_msgData_558_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5_spec__7___boxed(lean_object* v_msgData_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5_spec__7(v_msgData_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_579_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_580_; double v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_float_of_nat(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg(lean_object* v_cls_585_, lean_object* v_msg_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_ref_592_; lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_638_; 
v_ref_592_ = lean_ctor_get(v___y_589_, 5);
v___x_593_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5_spec__7(v_msg_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_638_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_638_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_638_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v_traceState_599_; lean_object* v_env_600_; lean_object* v_nextMacroScope_601_; lean_object* v_ngen_602_; lean_object* v_auxDeclNGen_603_; lean_object* v_cache_604_; lean_object* v_messages_605_; lean_object* v_infoState_606_; lean_object* v_snapshotTasks_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_637_; 
v___x_598_ = lean_st_ref_take(v___y_590_);
v_traceState_599_ = lean_ctor_get(v___x_598_, 4);
v_env_600_ = lean_ctor_get(v___x_598_, 0);
v_nextMacroScope_601_ = lean_ctor_get(v___x_598_, 1);
v_ngen_602_ = lean_ctor_get(v___x_598_, 2);
v_auxDeclNGen_603_ = lean_ctor_get(v___x_598_, 3);
v_cache_604_ = lean_ctor_get(v___x_598_, 5);
v_messages_605_ = lean_ctor_get(v___x_598_, 6);
v_infoState_606_ = lean_ctor_get(v___x_598_, 7);
v_snapshotTasks_607_ = lean_ctor_get(v___x_598_, 8);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_637_ == 0)
{
v___x_609_ = v___x_598_;
v_isShared_610_ = v_isSharedCheck_637_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snapshotTasks_607_);
lean_inc(v_infoState_606_);
lean_inc(v_messages_605_);
lean_inc(v_cache_604_);
lean_inc(v_traceState_599_);
lean_inc(v_auxDeclNGen_603_);
lean_inc(v_ngen_602_);
lean_inc(v_nextMacroScope_601_);
lean_inc(v_env_600_);
lean_dec(v___x_598_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_637_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
uint64_t v_tid_611_; lean_object* v_traces_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_636_; 
v_tid_611_ = lean_ctor_get_uint64(v_traceState_599_, sizeof(void*)*1);
v_traces_612_ = lean_ctor_get(v_traceState_599_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v_traceState_599_);
if (v_isSharedCheck_636_ == 0)
{
v___x_614_ = v_traceState_599_;
v_isShared_615_ = v_isSharedCheck_636_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_traces_612_);
lean_dec(v_traceState_599_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_636_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; double v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_616_ = lean_box(0);
v___x_617_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__0);
v___x_618_ = 0;
v___x_619_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__1));
v___x_620_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_620_, 0, v_cls_585_);
lean_ctor_set(v___x_620_, 1, v___x_616_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
lean_ctor_set_float(v___x_620_, sizeof(void*)*3, v___x_617_);
lean_ctor_set_float(v___x_620_, sizeof(void*)*3 + 8, v___x_617_);
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*3 + 16, v___x_618_);
v___x_621_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___closed__2));
v___x_622_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v_a_594_);
lean_ctor_set(v___x_622_, 2, v___x_621_);
lean_inc(v_ref_592_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_ref_592_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_PersistentArray_push___redArg(v_traces_612_, v___x_623_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_624_);
v___x_626_ = v___x_614_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_624_);
lean_ctor_set_uint64(v_reuseFailAlloc_635_, sizeof(void*)*1, v_tid_611_);
v___x_626_ = v_reuseFailAlloc_635_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v___x_626_);
v___x_628_ = v___x_609_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_env_600_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_nextMacroScope_601_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_ngen_602_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_auxDeclNGen_603_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_634_, 5, v_cache_604_);
lean_ctor_set(v_reuseFailAlloc_634_, 6, v_messages_605_);
lean_ctor_set(v_reuseFailAlloc_634_, 7, v_infoState_606_);
lean_ctor_set(v_reuseFailAlloc_634_, 8, v_snapshotTasks_607_);
v___x_628_ = v_reuseFailAlloc_634_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_629_ = lean_st_ref_set(v___y_590_, v___x_628_);
v___x_630_ = lean_box(0);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_630_);
v___x_632_ = v___x_596_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg___boxed(lean_object* v_cls_639_, lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg(v_cls_639_, v_msg_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_646_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3));
v___x_654_ = l_Lean_stringToMessageData(v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object* v___x_655_, lean_object* v_e_656_, lean_object* v_as_657_, size_t v_sz_658_, size_t v_i_659_, lean_object* v_b_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_a_673_; uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_lt(v_i_659_, v_sz_658_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_e_656_);
lean_dec(v___x_655_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_b_660_);
return v___x_678_;
}
else
{
lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_785_; 
v_snd_679_ = lean_ctor_get(v_b_660_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_b_660_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_b_660_, 0);
lean_dec(v_unused_786_);
v___x_681_ = v_b_660_;
v_isShared_682_ = v_isSharedCheck_785_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_dec(v_b_660_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_785_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_array_683_; lean_object* v_start_684_; lean_object* v_stop_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_array_683_ = lean_ctor_get(v_snd_679_, 0);
v_start_684_ = lean_ctor_get(v_snd_679_, 1);
v_stop_685_ = lean_ctor_get(v_snd_679_, 2);
v___x_686_ = lean_box(0);
v___x_687_ = lean_nat_dec_lt(v_start_684_, v_stop_685_);
if (v___x_687_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_e_656_);
lean_dec(v___x_655_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_686_);
v___x_689_ = v___x_681_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_snd_679_);
v___x_689_ = v_reuseFailAlloc_691_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; 
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
else
{
lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_781_; 
lean_inc(v_stop_685_);
lean_inc(v_start_684_);
lean_inc_ref(v_array_683_);
v_isSharedCheck_781_ = !lean_is_exclusive(v_snd_679_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_782_ = lean_ctor_get(v_snd_679_, 2);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_snd_679_, 1);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_snd_679_, 0);
lean_dec(v_unused_784_);
v___x_693_ = v_snd_679_;
v_isShared_694_ = v_isSharedCheck_781_;
goto v_resetjp_692_;
}
else
{
lean_dec(v_snd_679_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_781_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_695_ = lean_array_uget_borrowed(v_as_657_, v_i_659_);
v___x_696_ = l_Lean_Expr_mvarId_x21(v_a_695_);
v___x_697_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_696_, v___y_668_);
lean_dec(v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_772_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_772_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_772_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_772_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_702_ = lean_array_fget(v_array_683_, v_start_684_);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_add(v_start_684_, v___x_703_);
lean_dec(v_start_684_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_704_);
v___x_706_ = v___x_693_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_array_683_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_stop_685_);
v___x_706_ = v_reuseFailAlloc_771_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
uint8_t v___y_718_; uint8_t v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_unbox(v___x_702_);
lean_dec(v___x_702_);
v___x_769_ = l_Lean_BinderInfo_isInstImplicit(v___x_768_);
if (v___x_769_ == 0)
{
lean_dec(v_a_698_);
v___y_718_ = v___x_769_;
goto v___jp_717_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = lean_unbox(v_a_698_);
lean_dec(v_a_698_);
if (v___x_770_ == 0)
{
v___y_718_ = v___x_769_;
goto v___jp_717_;
}
else
{
lean_del_object(v___x_700_);
lean_del_object(v___x_681_);
goto v___jp_715_;
}
}
v___jp_707_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0));
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_706_);
lean_ctor_set(v___x_681_, 0, v___x_708_);
v___x_710_ = v___x_681_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_706_);
v___x_710_ = v_reuseFailAlloc_714_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_710_);
v___x_712_ = v___x_700_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
v___jp_715_:
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_686_);
lean_ctor_set(v___x_716_, 1, v___x_706_);
v_a_673_ = v___x_716_;
goto v___jp_672_;
}
v___jp_717_:
{
if (v___y_718_ == 0)
{
lean_del_object(v___x_700_);
lean_del_object(v___x_681_);
goto v___jp_715_;
}
else
{
lean_object* v___x_719_; 
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v_a_695_);
v___x_719_ = lean_infer_type(v_a_695_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_719_);
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v_a_695_);
v___x_721_ = l_Lean_Meta_Grind_synthInstanceAndAssign___redArg(v_a_695_, v_a_720_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; uint8_t v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref(v___x_721_);
v___x_723_ = lean_unbox(v_a_722_);
lean_dec(v_a_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_663_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; uint8_t v_verbose_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v___x_724_);
v_verbose_726_ = lean_ctor_get_uint8(v_a_725_, sizeof(void*)*11 + 15);
lean_dec(v_a_725_);
if (v_verbose_726_ == 0)
{
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_e_656_);
lean_dec(v___x_655_);
goto v___jp_707_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_727_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
v___x_728_ = l_Lean_MessageData_ofName(v___x_655_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_indentExpr(v_e_656_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_Meta_Grind_reportIssue(v___x_733_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_dec_ref(v___x_734_);
goto v___jp_707_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v___x_706_);
lean_del_object(v___x_700_);
lean_del_object(v___x_681_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v___x_706_);
lean_del_object(v___x_700_);
lean_del_object(v___x_681_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_e_656_);
lean_dec(v___x_655_);
v_a_743_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_724_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_724_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v___x_751_; 
lean_del_object(v___x_700_);
lean_del_object(v___x_681_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_686_);
lean_ctor_set(v___x_751_, 1, v___x_706_);
v_a_673_ = v___x_751_;
goto v___jp_672_;
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v___x_706_);
lean_del_object(v___x_700_);
lean_del_object(v___x_681_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_e_656_);
lean_dec(v___x_655_);
v_a_752_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_721_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_721_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v___x_706_);
lean_del_object(v___x_700_);
lean_del_object(v___x_681_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_e_656_);
lean_dec(v___x_655_);
v_a_760_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_719_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_719_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_del_object(v___x_693_);
lean_dec(v_stop_685_);
lean_dec(v_start_684_);
lean_dec_ref(v_array_683_);
lean_del_object(v___x_681_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_e_656_);
lean_dec(v___x_655_);
v_a_773_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_697_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_697_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
}
v___jp_672_:
{
size_t v___x_674_; size_t v___x_675_; 
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_659_, v___x_674_);
v_i_659_ = v___x_675_;
v_b_660_ = v_a_673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object** _args){
lean_object* v___x_787_ = _args[0];
lean_object* v_e_788_ = _args[1];
lean_object* v_as_789_ = _args[2];
lean_object* v_sz_790_ = _args[3];
lean_object* v_i_791_ = _args[4];
lean_object* v_b_792_ = _args[5];
lean_object* v___y_793_ = _args[6];
lean_object* v___y_794_ = _args[7];
lean_object* v___y_795_ = _args[8];
lean_object* v___y_796_ = _args[9];
lean_object* v___y_797_ = _args[10];
lean_object* v___y_798_ = _args[11];
lean_object* v___y_799_ = _args[12];
lean_object* v___y_800_ = _args[13];
lean_object* v___y_801_ = _args[14];
lean_object* v___y_802_ = _args[15];
lean_object* v___y_803_ = _args[16];
_start:
{
size_t v_sz_boxed_804_; size_t v_i_boxed_805_; lean_object* v_res_806_; 
v_sz_boxed_804_ = lean_unbox_usize(v_sz_790_);
lean_dec(v_sz_790_);
v_i_boxed_805_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_787_, v_e_788_, v_as_789_, v_sz_boxed_804_, v_i_boxed_805_, v_b_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v_as_789_);
return v_res_806_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5));
v___x_817_ = l_Lean_stringToMessageData(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7));
v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
return v___x_820_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9));
v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11));
v___x_826_ = l_Lean_stringToMessageData(v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15));
v___x_835_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14));
v___x_836_ = l_Lean_mkConst(v___x_835_, v___x_834_);
return v___x_836_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18(void){
_start:
{
uint8_t v___x_839_; uint64_t v___x_840_; 
v___x_839_ = 1;
v___x_840_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object* v_e_841_, lean_object* v_thm_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_841_, v___y_843_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v___x_868_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_845_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_1206_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_1206_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_1206_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint8_t v___x_873_; 
v___x_873_ = lean_nat_dec_lt(v_a_867_, v_a_869_);
lean_dec(v_a_869_);
lean_dec(v_a_867_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_thm_842_);
lean_dec_ref(v_e_841_);
v___x_874_ = lean_box(0);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_874_);
v___x_876_ = v___x_871_;
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
else
{
lean_object* v___x_878_; uint8_t v___x_879_; 
lean_del_object(v___x_871_);
lean_inc_ref(v_e_841_);
v___x_878_ = l_Lean_Expr_cleanupAnnotations(v_e_841_);
v___x_879_ = l_Lean_Expr_isApp(v___x_878_);
if (v___x_879_ == 0)
{
lean_dec_ref(v___x_878_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_thm_842_);
lean_dec_ref(v_e_841_);
goto v___jp_863_;
}
else
{
lean_object* v_arg_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_arg_880_ = lean_ctor_get(v___x_878_, 1);
lean_inc_ref(v_arg_880_);
v___x_881_ = l_Lean_Expr_appFnCleanup___redArg(v___x_878_);
v___x_882_ = l_Lean_Expr_isApp(v___x_881_);
if (v___x_882_ == 0)
{
lean_dec_ref(v___x_881_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_thm_842_);
lean_dec_ref(v_e_841_);
goto v___jp_863_;
}
else
{
lean_object* v_arg_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_arg_883_ = lean_ctor_get(v___x_881_, 1);
lean_inc_ref(v_arg_883_);
v___x_884_ = l_Lean_Expr_appFnCleanup___redArg(v___x_881_);
v___x_885_ = l_Lean_Expr_isApp(v___x_884_);
if (v___x_885_ == 0)
{
lean_dec_ref(v___x_884_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_thm_842_);
lean_dec_ref(v_e_841_);
goto v___jp_863_;
}
else
{
lean_object* v_arg_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_arg_886_ = lean_ctor_get(v___x_884_, 1);
lean_inc_ref(v_arg_886_);
v___x_887_ = l_Lean_Expr_appFnCleanup___redArg(v___x_884_);
v___x_888_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1));
v___x_889_ = l_Lean_Expr_isConstOf(v___x_887_, v___x_888_);
lean_dec_ref(v___x_887_);
if (v___x_889_ == 0)
{
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_thm_842_);
lean_dec_ref(v_e_841_);
goto v___jp_863_;
}
else
{
lean_object* v_declName_890_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_919_; lean_object* v___y_920_; uint8_t v___y_921_; uint8_t v___y_954_; lean_object* v___y_955_; lean_object* v_a_956_; uint8_t v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_997_; lean_object* v___x_1021_; 
v_declName_890_ = lean_ctor_get(v_thm_842_, 0);
lean_inc(v_declName_890_);
lean_dec_ref(v_thm_842_);
lean_inc_ref(v___y_851_);
lean_inc(v_declName_890_);
v___x_1021_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_890_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; uint8_t v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v_a_1099_; lean_object* v___x_1130_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v_a_1022_);
v___x_1130_ = lean_infer_type(v_a_1022_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; uint8_t v_foApprox_1133_; uint8_t v_ctxApprox_1134_; uint8_t v_quasiPatternApprox_1135_; uint8_t v_constApprox_1136_; uint8_t v_isDefEqStuckEx_1137_; uint8_t v_unificationHints_1138_; uint8_t v_proofIrrelevance_1139_; uint8_t v_assignSyntheticOpaque_1140_; uint8_t v_offsetCnstrs_1141_; uint8_t v_etaStruct_1142_; uint8_t v_univApprox_1143_; uint8_t v_iota_1144_; uint8_t v_beta_1145_; uint8_t v_proj_1146_; uint8_t v_zeta_1147_; uint8_t v_zetaDelta_1148_; uint8_t v_zetaUnused_1149_; uint8_t v_zetaHave_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1189_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = l_Lean_Meta_Context_config(v___y_849_);
v_foApprox_1133_ = lean_ctor_get_uint8(v___x_1132_, 0);
v_ctxApprox_1134_ = lean_ctor_get_uint8(v___x_1132_, 1);
v_quasiPatternApprox_1135_ = lean_ctor_get_uint8(v___x_1132_, 2);
v_constApprox_1136_ = lean_ctor_get_uint8(v___x_1132_, 3);
v_isDefEqStuckEx_1137_ = lean_ctor_get_uint8(v___x_1132_, 4);
v_unificationHints_1138_ = lean_ctor_get_uint8(v___x_1132_, 5);
v_proofIrrelevance_1139_ = lean_ctor_get_uint8(v___x_1132_, 6);
v_assignSyntheticOpaque_1140_ = lean_ctor_get_uint8(v___x_1132_, 7);
v_offsetCnstrs_1141_ = lean_ctor_get_uint8(v___x_1132_, 8);
v_etaStruct_1142_ = lean_ctor_get_uint8(v___x_1132_, 10);
v_univApprox_1143_ = lean_ctor_get_uint8(v___x_1132_, 11);
v_iota_1144_ = lean_ctor_get_uint8(v___x_1132_, 12);
v_beta_1145_ = lean_ctor_get_uint8(v___x_1132_, 13);
v_proj_1146_ = lean_ctor_get_uint8(v___x_1132_, 14);
v_zeta_1147_ = lean_ctor_get_uint8(v___x_1132_, 15);
v_zetaDelta_1148_ = lean_ctor_get_uint8(v___x_1132_, 16);
v_zetaUnused_1149_ = lean_ctor_get_uint8(v___x_1132_, 17);
v_zetaHave_1150_ = lean_ctor_get_uint8(v___x_1132_, 18);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1152_ = v___x_1132_;
v_isShared_1153_ = v_isSharedCheck_1189_;
goto v_resetjp_1151_;
}
else
{
lean_dec(v___x_1132_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1189_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v_trackZetaDelta_1154_; lean_object* v_zetaDeltaSet_1155_; lean_object* v_lctx_1156_; lean_object* v_localInstances_1157_; lean_object* v_defEqCtx_x3f_1158_; lean_object* v_synthPendingDepth_1159_; lean_object* v_canUnfold_x3f_1160_; uint8_t v_univApprox_1161_; uint8_t v_inTypeClassResolution_1162_; uint8_t v_cacheInferType_1163_; uint8_t v___x_1164_; lean_object* v_config_1166_; 
v_trackZetaDelta_1154_ = lean_ctor_get_uint8(v___y_849_, sizeof(void*)*7);
v_zetaDeltaSet_1155_ = lean_ctor_get(v___y_849_, 1);
v_lctx_1156_ = lean_ctor_get(v___y_849_, 2);
v_localInstances_1157_ = lean_ctor_get(v___y_849_, 3);
v_defEqCtx_x3f_1158_ = lean_ctor_get(v___y_849_, 4);
v_synthPendingDepth_1159_ = lean_ctor_get(v___y_849_, 5);
v_canUnfold_x3f_1160_ = lean_ctor_get(v___y_849_, 6);
v_univApprox_1161_ = lean_ctor_get_uint8(v___y_849_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1162_ = lean_ctor_get_uint8(v___y_849_, sizeof(void*)*7 + 2);
v_cacheInferType_1163_ = lean_ctor_get_uint8(v___y_849_, sizeof(void*)*7 + 3);
v___x_1164_ = 1;
if (v_isShared_1153_ == 0)
{
v_config_1166_ = v___x_1152_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 0, v_foApprox_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 1, v_ctxApprox_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 2, v_quasiPatternApprox_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 3, v_constApprox_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 4, v_isDefEqStuckEx_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 5, v_unificationHints_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 6, v_proofIrrelevance_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 7, v_assignSyntheticOpaque_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 8, v_offsetCnstrs_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 10, v_etaStruct_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 11, v_univApprox_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 12, v_iota_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 13, v_beta_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 14, v_proj_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 15, v_zeta_1147_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 16, v_zetaDelta_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 17, v_zetaUnused_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, 18, v_zetaHave_1150_);
v_config_1166_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
uint64_t v___x_1167_; uint64_t v___x_1168_; uint64_t v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; uint64_t v_key_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_ctor_set_uint8(v_config_1166_, 9, v___x_1164_);
v___x_1167_ = l_Lean_Meta_Context_configKey(v___y_849_);
v___x_1168_ = 2ULL;
v___x_1169_ = lean_uint64_shift_right(v___x_1167_, v___x_1168_);
v___x_1170_ = lean_box(0);
v___x_1171_ = 0;
v___x_1172_ = lean_uint64_shift_left(v___x_1169_, v___x_1168_);
v___x_1173_ = lean_uint64_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18);
v_key_1174_ = lean_uint64_lor(v___x_1172_, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1175_, 0, v_config_1166_);
lean_ctor_set_uint64(v___x_1175_, sizeof(void*)*1, v_key_1174_);
lean_inc(v_canUnfold_x3f_1160_);
lean_inc(v_synthPendingDepth_1159_);
lean_inc(v_defEqCtx_x3f_1158_);
lean_inc_ref(v_localInstances_1157_);
lean_inc_ref(v_lctx_1156_);
lean_inc(v_zetaDeltaSet_1155_);
v___x_1176_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v_zetaDeltaSet_1155_);
lean_ctor_set(v___x_1176_, 2, v_lctx_1156_);
lean_ctor_set(v___x_1176_, 3, v_localInstances_1157_);
lean_ctor_set(v___x_1176_, 4, v_defEqCtx_x3f_1158_);
lean_ctor_set(v___x_1176_, 5, v_synthPendingDepth_1159_);
lean_ctor_set(v___x_1176_, 6, v_canUnfold_x3f_1160_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*7, v_trackZetaDelta_1154_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*7 + 1, v_univApprox_1161_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1162_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*7 + 3, v_cacheInferType_1163_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
v___x_1177_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1131_, v___x_1170_, v___x_1171_, v___x_1176_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
v_a_1099_ = v_a_1178_;
goto v___jp_1098_;
}
else
{
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1179_; 
v_a_1179_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1179_);
lean_dec_ref(v___x_1177_);
v_a_1099_ = v_a_1179_;
goto v___jp_1098_;
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_1180_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1177_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1177_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_1190_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1130_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1130_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
v___jp_1023_:
{
if (lean_obj_tag(v___y_1028_) == 0)
{
lean_object* v_a_1029_; uint8_t v___x_1030_; 
v_a_1029_ = lean_ctor_get(v___y_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___y_1028_);
v___x_1030_ = lean_unbox(v_a_1029_);
lean_dec(v_a_1029_);
if (v___x_1030_ == 0)
{
lean_dec_ref(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v_a_1022_);
lean_dec(v___y_843_);
v___y_997_ = v___y_1025_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; size_t v_sz_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v___y_1025_);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_array_get_size(v___y_1027_);
v___x_1033_ = l_Array_toSubarray___redArg(v___y_1027_, v___x_1031_, v___x_1032_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_1033_);
v_sz_1036_ = lean_array_size(v___y_1026_);
v___x_1037_ = ((size_t)0ULL);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc_ref(v_e_841_);
lean_inc(v_declName_890_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_890_, v_e_841_, v___y_1026_, v_sz_1036_, v___x_1037_, v___x_1035_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1081_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1081_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1081_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_fst_1043_; 
v_fst_1043_ = lean_ctor_get(v_a_1039_, 0);
lean_inc(v_fst_1043_);
lean_dec(v_a_1039_);
if (lean_obj_tag(v_fst_1043_) == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_a_1046_; lean_object* v___x_1047_; 
lean_del_object(v___x_1041_);
v___x_1044_ = l_Lean_mkAppN(v_a_1022_, v___y_1026_);
v___x_1045_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_1044_, v___y_850_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v___x_1045_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc(v___y_843_);
lean_inc_ref(v_e_841_);
v___x_1047_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_847_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref(v___x_1049_);
v___x_1051_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16);
lean_inc_ref(v_e_841_);
v___x_1052_ = l_Lean_mkApp4(v___x_1051_, v_e_841_, v_a_1050_, v_a_1048_, v_a_1046_);
v___x_1053_ = lean_array_get_size(v___y_1026_);
v___x_1054_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17));
v___x_1055_ = lean_nat_dec_lt(v___x_1031_, v___x_1053_);
if (v___x_1055_ == 0)
{
lean_dec_ref(v___y_1026_);
v___y_954_ = v___y_1024_;
v___y_955_ = v___x_1052_;
v_a_956_ = v___x_1054_;
goto v___jp_953_;
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_le(v___x_1053_, v___x_1053_);
if (v___x_1056_ == 0)
{
if (v___x_1055_ == 0)
{
lean_dec_ref(v___y_1026_);
v___y_954_ = v___y_1024_;
v___y_955_ = v___x_1052_;
v_a_956_ = v___x_1054_;
goto v___jp_953_;
}
else
{
size_t v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_usize_of_nat(v___x_1053_);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(v___y_1026_, v___x_1037_, v___x_1057_, v___x_1054_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec_ref(v___y_1026_);
v___y_984_ = v___y_1024_;
v___y_985_ = v___x_1052_;
v___y_986_ = v___x_1058_;
goto v___jp_983_;
}
}
else
{
size_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_usize_of_nat(v___x_1053_);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(v___y_1026_, v___x_1037_, v___x_1059_, v___x_1054_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec_ref(v___y_1026_);
v___y_984_ = v___y_1024_;
v___y_985_ = v___x_1052_;
v___y_986_ = v___x_1060_;
goto v___jp_983_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1048_);
lean_dec(v_a_1046_);
lean_dec_ref(v___y_1026_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_1061_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1049_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1049_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v_a_1046_);
lean_dec_ref(v___y_1026_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_1069_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1047_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1047_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_val_1077_; lean_object* v___x_1079_; 
lean_dec_ref(v___y_1026_);
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_val_1077_ = lean_ctor_get(v_fst_1043_, 0);
lean_inc(v_val_1077_);
lean_dec_ref(v_fst_1043_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_val_1077_);
v___x_1079_ = v___x_1041_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_val_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v___y_1026_);
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_1082_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1038_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1038_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
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
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_1090_ = lean_ctor_get(v___y_1028_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___y_1028_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___y_1028_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___y_1028_);
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
v___jp_1098_:
{
lean_object* v_snd_1100_; lean_object* v_fst_1101_; lean_object* v_fst_1102_; lean_object* v_snd_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_snd_1100_ = lean_ctor_get(v_a_1099_, 1);
lean_inc(v_snd_1100_);
v_fst_1101_ = lean_ctor_get(v_a_1099_, 0);
lean_inc(v_fst_1101_);
lean_dec_ref(v_a_1099_);
v_fst_1102_ = lean_ctor_get(v_snd_1100_, 0);
lean_inc(v_fst_1102_);
v_snd_1103_ = lean_ctor_get(v_snd_1100_, 1);
lean_inc(v_snd_1103_);
lean_dec(v_snd_1100_);
lean_inc(v_snd_1103_);
v___x_1104_ = l_Lean_Expr_cleanupAnnotations(v_snd_1103_);
v___x_1105_ = l_Lean_Expr_isApp(v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v___x_1104_);
lean_dec(v_snd_1103_);
lean_dec(v_fst_1102_);
lean_dec(v_fst_1101_);
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
goto v___jp_860_;
}
else
{
lean_object* v_arg_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_arg_1106_ = lean_ctor_get(v___x_1104_, 1);
lean_inc_ref(v_arg_1106_);
v___x_1107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1104_);
v___x_1108_ = l_Lean_Expr_isApp(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_arg_1106_);
lean_dec(v_snd_1103_);
lean_dec(v_fst_1102_);
lean_dec(v_fst_1101_);
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
goto v___jp_860_;
}
else
{
lean_object* v_arg_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_arg_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc_ref(v_arg_1109_);
v___x_1110_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1107_);
v___x_1111_ = l_Lean_Expr_isApp(v___x_1110_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_arg_1109_);
lean_dec_ref(v_arg_1106_);
lean_dec(v_snd_1103_);
lean_dec(v_fst_1102_);
lean_dec(v_fst_1101_);
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
goto v___jp_860_;
}
else
{
lean_object* v_arg_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_arg_1112_ = lean_ctor_get(v___x_1110_, 1);
lean_inc_ref(v_arg_1112_);
v___x_1113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1110_);
v___x_1114_ = l_Lean_Expr_isConstOf(v___x_1113_, v___x_888_);
lean_dec_ref(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_arg_1109_);
lean_dec_ref(v_arg_1106_);
lean_dec(v_snd_1103_);
lean_dec(v_fst_1102_);
lean_dec(v_fst_1101_);
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
goto v___jp_860_;
}
else
{
lean_object* v___x_1115_; 
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
v___x_1115_ = l_Lean_Meta_isExprDefEq(v_arg_886_, v_arg_1112_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; uint8_t v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
v___x_1117_ = lean_unbox(v_a_1116_);
lean_dec(v_a_1116_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v_arg_1109_);
lean_dec_ref(v_arg_1106_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
v___y_1024_ = v___x_1114_;
v___y_1025_ = v_snd_1103_;
v___y_1026_ = v_fst_1101_;
v___y_1027_ = v_fst_1102_;
v___y_1028_ = v___x_1115_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1118_; 
lean_dec_ref(v___x_1115_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
v___x_1118_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1114_, v_arg_1109_, v_arg_883_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; uint8_t v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = lean_unbox(v_a_1119_);
lean_dec(v_a_1119_);
if (v___x_1120_ == 0)
{
lean_dec_ref(v_arg_1106_);
lean_dec(v_fst_1102_);
lean_dec(v_fst_1101_);
lean_dec(v_a_1022_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_843_);
v___y_997_ = v_snd_1103_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1121_; 
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
v___x_1121_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1114_, v_arg_1106_, v_arg_880_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
v___y_1024_ = v___x_1114_;
v___y_1025_ = v_snd_1103_;
v___y_1026_ = v_fst_1101_;
v___y_1027_ = v_fst_1102_;
v___y_1028_ = v___x_1121_;
goto v___jp_1023_;
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_arg_1106_);
lean_dec(v_snd_1103_);
lean_dec(v_fst_1102_);
lean_dec(v_fst_1101_);
lean_dec(v_a_1022_);
lean_dec(v_declName_890_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_1122_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1118_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1118_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1109_);
lean_dec_ref(v_arg_1106_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
v___y_1024_ = v___x_1114_;
v___y_1025_ = v_snd_1103_;
v___y_1026_ = v_fst_1101_;
v___y_1027_ = v_fst_1102_;
v___y_1028_ = v___x_1115_;
goto v___jp_1023_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v_declName_890_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
lean_dec_ref(v_arg_880_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_1198_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1021_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1021_);
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
v___jp_891_:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_841_, v___y_894_);
lean_dec_ref(v_e_841_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v___x_904_);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_add(v_a_905_, v___x_906_);
lean_dec(v_a_905_);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v_declName_890_);
v___x_909_ = l_Lean_Meta_Grind_addNewRawFact(v___y_893_, v___y_892_, v___x_907_, v___x_908_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec(v___y_894_);
return v___x_909_;
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v_declName_890_);
v_a_910_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_904_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_904_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
v___jp_918_:
{
if (v___y_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_a_924_; uint8_t v___x_925_; 
v___x_922_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_923_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_922_, v___y_851_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_923_);
v___x_925_ = lean_unbox(v_a_924_);
lean_dec(v_a_924_);
if (v___x_925_ == 0)
{
v___y_892_ = v___y_919_;
v___y_893_ = v___y_920_;
v___y_894_ = v___y_843_;
v___y_895_ = v___y_844_;
v___y_896_ = v___y_845_;
v___y_897_ = v___y_846_;
v___y_898_ = v___y_847_;
v___y_899_ = v___y_848_;
v___y_900_ = v___y_849_;
v___y_901_ = v___y_850_;
v___y_902_ = v___y_851_;
v___y_903_ = v___y_852_;
goto v___jp_891_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_inc(v_declName_890_);
v___x_926_ = l_Lean_MessageData_ofName(v_declName_890_);
v___x_927_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
lean_inc_ref(v___y_919_);
v___x_929_ = l_Lean_MessageData_ofExpr(v___y_919_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg(v___x_922_, v___x_930_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_dec_ref(v___x_931_);
v___y_892_ = v___y_919_;
v___y_893_ = v___y_920_;
v___y_894_ = v___y_843_;
v___y_895_ = v___y_844_;
v___y_896_ = v___y_845_;
v___y_897_ = v___y_846_;
v___y_898_ = v___y_847_;
v___y_899_ = v___y_848_;
v___y_900_ = v___y_849_;
v___y_901_ = v___y_850_;
v___y_902_ = v___y_851_;
v___y_903_ = v___y_852_;
goto v___jp_891_;
}
else
{
lean_dec_ref(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
return v___x_931_;
}
}
}
else
{
lean_object* v___x_932_; 
lean_dec_ref(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_843_);
v___x_932_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_845_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; uint8_t v_verbose_934_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref(v___x_932_);
v_verbose_934_ = lean_ctor_get_uint8(v_a_933_, sizeof(void*)*11 + 15);
lean_dec(v_a_933_);
if (v_verbose_934_ == 0)
{
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v_e_841_);
goto v___jp_854_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_935_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8);
v___x_936_ = l_Lean_MessageData_ofName(v_declName_890_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_indentExpr(v_e_841_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_Meta_Grind_reportIssue(v___x_943_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_dec_ref(v___x_944_);
goto v___jp_854_;
}
else
{
return v___x_944_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v_e_841_);
v_a_945_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_932_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_932_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
v___jp_953_:
{
uint8_t v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; 
v___x_957_ = 0;
v___x_958_ = 1;
v___x_959_ = l_Lean_Meta_mkLambdaFVars(v_a_956_, v___y_955_, v___x_957_, v___y_954_, v___x_957_, v___y_954_, v___x_958_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec_ref(v_a_956_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_963_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v___x_961_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_960_, v___y_850_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v_a_962_);
v___x_963_ = lean_infer_type(v_a_962_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; uint8_t v___x_965_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref(v___x_963_);
v___x_965_ = l_Lean_Expr_hasMVar(v_a_962_);
if (v___x_965_ == 0)
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_Expr_hasMVar(v_a_964_);
v___y_919_ = v_a_964_;
v___y_920_ = v_a_962_;
v___y_921_ = v___x_966_;
goto v___jp_918_;
}
else
{
v___y_919_ = v_a_964_;
v___y_920_ = v_a_962_;
v___y_921_ = v___y_954_;
goto v___jp_918_;
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_a_962_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_967_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_963_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_963_);
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
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_975_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_959_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_959_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
v___jp_983_:
{
if (lean_obj_tag(v___y_986_) == 0)
{
lean_object* v_a_987_; 
v_a_987_ = lean_ctor_get(v___y_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref(v___y_986_);
v___y_954_ = v___y_984_;
v___y_955_ = v___y_985_;
v_a_956_ = v_a_987_;
goto v___jp_953_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___y_985_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_e_841_);
v_a_988_ = lean_ctor_get(v___y_986_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___y_986_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___y_986_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___y_986_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
v___jp_996_:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_845_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; uint8_t v_verbose_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v___x_998_);
v_verbose_1000_ = lean_ctor_get_uint8(v_a_999_, sizeof(void*)*11 + 15);
lean_dec(v_a_999_);
if (v_verbose_1000_ == 0)
{
lean_dec_ref(v___y_997_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v_e_841_);
goto v___jp_857_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1001_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8);
v___x_1002_ = l_Lean_MessageData_ofName(v_declName_890_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_indentExpr(v_e_841_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_indentExpr(v___y_997_);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_Meta_Grind_reportIssue(v___x_1011_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_dec_ref(v___x_1012_);
goto v___jp_857_;
}
else
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v___y_997_);
lean_dec(v_declName_890_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v_e_841_);
v_a_1013_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_998_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_998_);
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_867_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_thm_842_);
lean_dec_ref(v_e_841_);
v_a_1207_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_868_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_868_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_thm_842_);
lean_dec_ref(v_e_841_);
v_a_1215_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_866_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_866_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
v___jp_854_:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
v___jp_857_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
v___jp_860_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
v___jp_863_:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object* v_e_1223_, lean_object* v_thm_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(v_e_1223_, v_thm_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object* v_thm_1237_, lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___f_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; 
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed), 13, 2);
lean_closure_set(v___f_1250_, 0, v_e_1238_);
lean_closure_set(v___f_1250_, 1, v_thm_1237_);
v___x_1251_ = 0;
v___x_1252_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__7___redArg(v___f_1250_, v___x_1251_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object* v_thm_1253_, lean_object* v_e_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_thm_1253_, v_e_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object* v_mvarId_1267_, lean_object* v_val_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_1267_, v_val_1268_, v___y_1276_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object* v_mvarId_1281_, lean_object* v_val_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(v_mvarId_1281_, v_val_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object* v_mvarId_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_1295_, v___y_1303_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object* v_mvarId_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(v_mvarId_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec(v_mvarId_1308_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object* v_cls_1321_, lean_object* v_msg_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___redArg(v_cls_1321_, v_msg_1322_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object* v_cls_1335_, lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_cls_1335_, v_msg_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_1350_, v_x_1351_, v_x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object* v_00_u03b2_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1355_, v_x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(v_00_u03b2_1358_, v_x_1359_, v_x_1360_);
lean_dec(v_x_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1363_, lean_object* v_x_1364_, size_t v_x_1365_, size_t v_x_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___redArg(v_x_1364_, v_x_1365_, v_x_1366_, v_x_1367_, v_x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_){
_start:
{
size_t v_x_235805__boxed_1376_; size_t v_x_235806__boxed_1377_; lean_object* v_res_1378_; 
v_x_235805__boxed_1376_ = lean_unbox_usize(v_x_1372_);
lean_dec(v_x_1372_);
v_x_235806__boxed_1377_ = lean_unbox_usize(v_x_1373_);
lean_dec(v_x_1373_);
v_res_1378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4(v_00_u03b2_1370_, v_x_1371_, v_x_235805__boxed_1376_, v_x_235806__boxed_1377_, v_x_1374_, v_x_1375_);
return v_res_1378_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_1379_, lean_object* v_x_1380_, size_t v_x_1381_, lean_object* v_x_1382_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___redArg(v_x_1380_, v_x_1381_, v_x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7___boxed(lean_object* v_00_u03b2_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
size_t v_x_235822__boxed_1388_; uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_x_235822__boxed_1388_ = lean_unbox_usize(v_x_1386_);
lean_dec(v_x_1386_);
v_res_1389_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7(v_00_u03b2_1384_, v_x_1385_, v_x_235822__boxed_1388_, v_x_1387_);
lean_dec(v_x_1387_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b2_1391_, lean_object* v_n_1392_, lean_object* v_k_1393_, lean_object* v_v_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10___redArg(v_n_1392_, v_k_1393_, v_v_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b2_1396_, size_t v_depth_1397_, lean_object* v_keys_1398_, lean_object* v_vals_1399_, lean_object* v_heq_1400_, lean_object* v_i_1401_, lean_object* v_entries_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___redArg(v_depth_1397_, v_keys_1398_, v_vals_1399_, v_i_1401_, v_entries_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b2_1404_, lean_object* v_depth_1405_, lean_object* v_keys_1406_, lean_object* v_vals_1407_, lean_object* v_heq_1408_, lean_object* v_i_1409_, lean_object* v_entries_1410_){
_start:
{
size_t v_depth_boxed_1411_; lean_object* v_res_1412_; 
v_depth_boxed_1411_ = lean_unbox_usize(v_depth_1405_);
lean_dec(v_depth_1405_);
v_res_1412_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__11(v_00_u03b2_1404_, v_depth_boxed_1411_, v_keys_1406_, v_vals_1407_, v_heq_1408_, v_i_1409_, v_entries_1410_);
lean_dec_ref(v_vals_1407_);
lean_dec_ref(v_keys_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14(lean_object* v_00_u03b2_1413_, lean_object* v_keys_1414_, lean_object* v_vals_1415_, lean_object* v_heq_1416_, lean_object* v_i_1417_, lean_object* v_k_1418_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___redArg(v_keys_1414_, v_i_1417_, v_k_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14___boxed(lean_object* v_00_u03b2_1420_, lean_object* v_keys_1421_, lean_object* v_vals_1422_, lean_object* v_heq_1423_, lean_object* v_i_1424_, lean_object* v_k_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__7_spec__14(v_00_u03b2_1420_, v_keys_1421_, v_vals_1422_, v_heq_1423_, v_i_1424_, v_k_1425_);
lean_dec(v_k_1425_);
lean_dec_ref(v_vals_1422_);
lean_dec_ref(v_keys_1421_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b2_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_x_1429_, v_x_1430_, v_x_1431_, v_x_1432_);
return v___x_1433_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
}
#ifdef __cplusplus
}
#endif
