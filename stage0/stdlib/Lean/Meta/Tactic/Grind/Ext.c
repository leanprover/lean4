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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getMaxGeneration___redArg(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to apply extensionality theorem `"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\nresulting terms contain metavariables"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\nis not definitionally equal to"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19;
static const lean_array_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(lean_object* v_k_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
lean_inc(v___y_62_);
lean_inc_ref(v___y_61_);
lean_inc(v___y_60_);
lean_inc_ref(v___y_59_);
lean_inc(v___y_58_);
lean_inc(v___y_57_);
v___x_68_ = lean_apply_11(v_k_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, lean_box(0));
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed(lean_object* v_k_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(v_k_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec(v___y_70_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(lean_object* v_k_82_, uint8_t v_allowLevelAssignments_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___f_95_; lean_object* v___x_96_; 
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc(v___y_84_);
v___f_95_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_95_, 0, v_k_82_);
lean_closure_set(v___f_95_, 1, v___y_84_);
lean_closure_set(v___f_95_, 2, v___y_85_);
lean_closure_set(v___f_95_, 3, v___y_86_);
lean_closure_set(v___f_95_, 4, v___y_87_);
lean_closure_set(v___f_95_, 5, v___y_88_);
lean_closure_set(v___f_95_, 6, v___y_89_);
v___x_96_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_83_, v___f_95_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_96_) == 0)
{
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___boxed(lean_object* v_k_105_, lean_object* v_allowLevelAssignments_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_118_; lean_object* v_res_119_; 
v_allowLevelAssignments_boxed_118_ = lean_unbox(v_allowLevelAssignments_106_);
v_res_119_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_105_, v_allowLevelAssignments_boxed_118_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec(v___y_107_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_object* v_00_u03b1_120_, lean_object* v_k_121_, uint8_t v_allowLevelAssignments_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_121_, v_allowLevelAssignments_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(lean_object* v_00_u03b1_135_, lean_object* v_k_136_, lean_object* v_allowLevelAssignments_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_149_; lean_object* v_res_150_; 
v_allowLevelAssignments_boxed_149_ = lean_unbox(v_allowLevelAssignments_137_);
v_res_150_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(v_00_u03b1_135_, v_k_136_, v_allowLevelAssignments_boxed_149_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec(v___y_138_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
lean_object* v_ks_155_; lean_object* v_vs_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_180_; 
v_ks_155_ = lean_ctor_get(v_x_151_, 0);
v_vs_156_ = lean_ctor_get(v_x_151_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_151_);
if (v_isSharedCheck_180_ == 0)
{
v___x_158_ = v_x_151_;
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_vs_156_);
lean_inc(v_ks_155_);
lean_dec(v_x_151_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_array_get_size(v_ks_155_);
v___x_161_ = lean_nat_dec_lt(v_x_152_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
lean_dec(v_x_152_);
v___x_162_ = lean_array_push(v_ks_155_, v_x_153_);
v___x_163_ = lean_array_push(v_vs_156_, v_x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_163_);
lean_ctor_set(v___x_158_, 0, v___x_162_);
v___x_165_ = v___x_158_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
else
{
lean_object* v_k_x27_167_; uint8_t v___x_168_; 
v_k_x27_167_ = lean_array_fget_borrowed(v_ks_155_, v_x_152_);
v___x_168_ = l_Lean_instBEqMVarId_beq(v_x_153_, v_k_x27_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_170_; 
if (v_isShared_159_ == 0)
{
v___x_170_ = v___x_158_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_ks_155_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_vs_156_);
v___x_170_ = v_reuseFailAlloc_174_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_x_152_, v___x_171_);
lean_dec(v_x_152_);
v_x_151_ = v___x_170_;
v_x_152_ = v___x_172_;
goto _start;
}
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_175_ = lean_array_fset(v_ks_155_, v_x_152_, v_x_153_);
v___x_176_ = lean_array_fset(v_vs_156_, v_x_152_, v_x_154_);
lean_dec(v_x_152_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_176_);
lean_ctor_set(v___x_158_, 0, v___x_175_);
v___x_178_ = v___x_158_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_n_181_, lean_object* v_k_182_, lean_object* v_v_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_n_181_, v___x_184_, v_k_182_, v_v_183_);
return v___x_185_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_186_; size_t v___x_187_; size_t v___x_188_; 
v___x_186_ = ((size_t)5ULL);
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_shift_left(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; 
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_191_ = lean_usize_sub(v___x_190_, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(lean_object* v_x_193_, size_t v_x_194_, size_t v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v_es_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v_j_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_es_198_ = lean_ctor_get(v_x_193_, 0);
v___x_199_ = ((size_t)5ULL);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_202_ = lean_usize_land(v_x_194_, v___x_201_);
v_j_203_ = lean_usize_to_nat(v___x_202_);
v___x_204_ = lean_array_get_size(v_es_198_);
v___x_205_ = lean_nat_dec_lt(v_j_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec(v_j_203_);
lean_dec(v_x_197_);
lean_dec(v_x_196_);
return v_x_193_;
}
else
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_242_; 
lean_inc_ref(v_es_198_);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v_x_193_, 0);
lean_dec(v_unused_243_);
v___x_207_ = v_x_193_;
v_isShared_208_ = v_isSharedCheck_242_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_x_193_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_242_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_v_209_; lean_object* v___x_210_; lean_object* v_xs_x27_211_; lean_object* v___y_213_; 
v_v_209_ = lean_array_fget(v_es_198_, v_j_203_);
v___x_210_ = lean_box(0);
v_xs_x27_211_ = lean_array_fset(v_es_198_, v_j_203_, v___x_210_);
switch(lean_obj_tag(v_v_209_))
{
case 0:
{
lean_object* v_key_218_; lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_229_; 
v_key_218_ = lean_ctor_get(v_v_209_, 0);
v_val_219_ = lean_ctor_get(v_v_209_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_v_209_);
if (v_isSharedCheck_229_ == 0)
{
v___x_221_ = v_v_209_;
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_inc(v_key_218_);
lean_dec(v_v_209_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_instBEqMVarId_beq(v_x_196_, v_key_218_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_221_);
v___x_224_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_218_, v_val_219_, v_x_196_, v_x_197_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___y_213_ = v___x_225_;
goto v___jp_212_;
}
else
{
lean_object* v___x_227_; 
lean_dec(v_val_219_);
lean_dec(v_key_218_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v_x_197_);
lean_ctor_set(v___x_221_, 0, v_x_196_);
v___x_227_ = v___x_221_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_x_196_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_x_197_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
v___y_213_ = v___x_227_;
goto v___jp_212_;
}
}
}
}
case 1:
{
lean_object* v_node_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_240_; 
v_node_230_ = lean_ctor_get(v_v_209_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v_v_209_);
if (v_isSharedCheck_240_ == 0)
{
v___x_232_ = v_v_209_;
v_isShared_233_ = v_isSharedCheck_240_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_node_230_);
lean_dec(v_v_209_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_240_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
size_t v___x_234_; size_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_234_ = lean_usize_shift_right(v_x_194_, v___x_199_);
v___x_235_ = lean_usize_add(v_x_195_, v___x_200_);
v___x_236_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_node_230_, v___x_234_, v___x_235_, v_x_196_, v_x_197_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_236_);
v___x_238_ = v___x_232_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
v___y_213_ = v___x_238_;
goto v___jp_212_;
}
}
}
default: 
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_x_196_);
lean_ctor_set(v___x_241_, 1, v_x_197_);
v___y_213_ = v___x_241_;
goto v___jp_212_;
}
}
v___jp_212_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_array_fset(v_xs_x27_211_, v_j_203_, v___y_213_);
lean_dec(v_j_203_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_214_);
v___x_216_ = v___x_207_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
else
{
lean_object* v_ks_244_; lean_object* v_vs_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_265_; 
v_ks_244_ = lean_ctor_get(v_x_193_, 0);
v_vs_245_ = lean_ctor_get(v_x_193_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_265_ == 0)
{
v___x_247_ = v_x_193_;
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_vs_245_);
lean_inc(v_ks_244_);
lean_dec(v_x_193_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_ks_244_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_vs_245_);
v___x_250_ = v_reuseFailAlloc_264_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v_newNode_251_; uint8_t v___y_253_; size_t v___x_259_; uint8_t v___x_260_; 
v_newNode_251_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v___x_250_, v_x_196_, v_x_197_);
v___x_259_ = ((size_t)7ULL);
v___x_260_ = lean_usize_dec_le(v___x_259_, v_x_195_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_251_);
v___x_262_ = lean_unsigned_to_nat(4u);
v___x_263_ = lean_nat_dec_lt(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
v___y_253_ = v___x_263_;
goto v___jp_252_;
}
else
{
v___y_253_ = v___x_260_;
goto v___jp_252_;
}
v___jp_252_:
{
if (v___y_253_ == 0)
{
lean_object* v_ks_254_; lean_object* v_vs_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_ks_254_ = lean_ctor_get(v_newNode_251_, 0);
lean_inc_ref(v_ks_254_);
v_vs_255_ = lean_ctor_get(v_newNode_251_, 1);
lean_inc_ref(v_vs_255_);
lean_dec_ref(v_newNode_251_);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_x_195_, v_ks_254_, v_vs_255_, v___x_256_, v___x_257_);
lean_dec_ref(v_vs_255_);
lean_dec_ref(v_ks_254_);
return v___x_258_;
}
else
{
return v_newNode_251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(size_t v_depth_266_, lean_object* v_keys_267_, lean_object* v_vals_268_, lean_object* v_i_269_, lean_object* v_entries_270_){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_array_get_size(v_keys_267_);
v___x_272_ = lean_nat_dec_lt(v_i_269_, v___x_271_);
if (v___x_272_ == 0)
{
lean_dec(v_i_269_);
return v_entries_270_;
}
else
{
lean_object* v_k_273_; lean_object* v_v_274_; uint64_t v___x_275_; size_t v_h_276_; size_t v___x_277_; lean_object* v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v_h_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_k_273_ = lean_array_fget_borrowed(v_keys_267_, v_i_269_);
v_v_274_ = lean_array_fget_borrowed(v_vals_268_, v_i_269_);
v___x_275_ = l_Lean_instHashableMVarId_hash(v_k_273_);
v_h_276_ = lean_uint64_to_usize(v___x_275_);
v___x_277_ = ((size_t)5ULL);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_sub(v_depth_266_, v___x_279_);
v___x_281_ = lean_usize_mul(v___x_277_, v___x_280_);
v_h_282_ = lean_usize_shift_right(v_h_276_, v___x_281_);
v___x_283_ = lean_nat_add(v_i_269_, v___x_278_);
lean_dec(v_i_269_);
lean_inc(v_v_274_);
lean_inc(v_k_273_);
v___x_284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_entries_270_, v_h_282_, v_depth_266_, v_k_273_, v_v_274_);
v_i_269_ = v___x_283_;
v_entries_270_ = v___x_284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_depth_286_, lean_object* v_keys_287_, lean_object* v_vals_288_, lean_object* v_i_289_, lean_object* v_entries_290_){
_start:
{
size_t v_depth_boxed_291_; lean_object* v_res_292_; 
v_depth_boxed_291_ = lean_unbox_usize(v_depth_286_);
lean_dec(v_depth_286_);
v_res_292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_boxed_291_, v_keys_287_, v_vals_288_, v_i_289_, v_entries_290_);
lean_dec_ref(v_vals_288_);
lean_dec_ref(v_keys_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
size_t v_x_214755__boxed_298_; size_t v_x_214756__boxed_299_; lean_object* v_res_300_; 
v_x_214755__boxed_298_ = lean_unbox_usize(v_x_294_);
lean_dec(v_x_294_);
v_x_214756__boxed_299_ = lean_unbox_usize(v_x_295_);
lean_dec(v_x_295_);
v_res_300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_293_, v_x_214755__boxed_298_, v_x_214756__boxed_299_, v_x_296_, v_x_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
uint64_t v___x_304_; size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; 
v___x_304_ = l_Lean_instHashableMVarId_hash(v_x_302_);
v___x_305_ = lean_uint64_to_usize(v___x_304_);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_301_, v___x_305_, v___x_306_, v_x_302_, v_x_303_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object* v_mvarId_308_, lean_object* v_val_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v_mctx_313_; lean_object* v_cache_314_; lean_object* v_zetaDeltaFVarIds_315_; lean_object* v_postponed_316_; lean_object* v_diag_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_345_; 
v___x_312_ = lean_st_ref_take(v___y_310_);
v_mctx_313_ = lean_ctor_get(v___x_312_, 0);
v_cache_314_ = lean_ctor_get(v___x_312_, 1);
v_zetaDeltaFVarIds_315_ = lean_ctor_get(v___x_312_, 2);
v_postponed_316_ = lean_ctor_get(v___x_312_, 3);
v_diag_317_ = lean_ctor_get(v___x_312_, 4);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_345_ == 0)
{
v___x_319_ = v___x_312_;
v_isShared_320_ = v_isSharedCheck_345_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_diag_317_);
lean_inc(v_postponed_316_);
lean_inc(v_zetaDeltaFVarIds_315_);
lean_inc(v_cache_314_);
lean_inc(v_mctx_313_);
lean_dec(v___x_312_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_345_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_depth_321_; lean_object* v_levelAssignDepth_322_; lean_object* v_lmvarCounter_323_; lean_object* v_mvarCounter_324_; lean_object* v_lDecls_325_; lean_object* v_decls_326_; lean_object* v_userNames_327_; lean_object* v_lAssignment_328_; lean_object* v_eAssignment_329_; lean_object* v_dAssignment_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_344_; 
v_depth_321_ = lean_ctor_get(v_mctx_313_, 0);
v_levelAssignDepth_322_ = lean_ctor_get(v_mctx_313_, 1);
v_lmvarCounter_323_ = lean_ctor_get(v_mctx_313_, 2);
v_mvarCounter_324_ = lean_ctor_get(v_mctx_313_, 3);
v_lDecls_325_ = lean_ctor_get(v_mctx_313_, 4);
v_decls_326_ = lean_ctor_get(v_mctx_313_, 5);
v_userNames_327_ = lean_ctor_get(v_mctx_313_, 6);
v_lAssignment_328_ = lean_ctor_get(v_mctx_313_, 7);
v_eAssignment_329_ = lean_ctor_get(v_mctx_313_, 8);
v_dAssignment_330_ = lean_ctor_get(v_mctx_313_, 9);
v_isSharedCheck_344_ = !lean_is_exclusive(v_mctx_313_);
if (v_isSharedCheck_344_ == 0)
{
v___x_332_ = v_mctx_313_;
v_isShared_333_ = v_isSharedCheck_344_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_dAssignment_330_);
lean_inc(v_eAssignment_329_);
lean_inc(v_lAssignment_328_);
lean_inc(v_userNames_327_);
lean_inc(v_decls_326_);
lean_inc(v_lDecls_325_);
lean_inc(v_mvarCounter_324_);
lean_inc(v_lmvarCounter_323_);
lean_inc(v_levelAssignDepth_322_);
lean_inc(v_depth_321_);
lean_dec(v_mctx_313_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_344_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_eAssignment_329_, v_mvarId_308_, v_val_309_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 8, v___x_334_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_depth_321_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_levelAssignDepth_322_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_lmvarCounter_323_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_mvarCounter_324_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_lDecls_325_);
lean_ctor_set(v_reuseFailAlloc_343_, 5, v_decls_326_);
lean_ctor_set(v_reuseFailAlloc_343_, 6, v_userNames_327_);
lean_ctor_set(v_reuseFailAlloc_343_, 7, v_lAssignment_328_);
lean_ctor_set(v_reuseFailAlloc_343_, 8, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_343_, 9, v_dAssignment_330_);
v___x_336_ = v_reuseFailAlloc_343_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_336_);
v___x_338_ = v___x_319_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_cache_314_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_zetaDeltaFVarIds_315_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_postponed_316_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_diag_317_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_st_ref_set(v___y_310_, v___x_338_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object* v_mvarId_346_, lean_object* v_val_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_346_, v_val_347_, v___y_348_);
lean_dec(v___y_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(uint8_t v___x_351_, lean_object* v_p_352_, lean_object* v_e_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = l_Lean_Expr_isMVar(v_p_352_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_isExprDefEq(v_p_352_, v_e_353_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
v___x_367_ = l_Lean_Expr_mvarId_x21(v_p_352_);
lean_dec_ref(v_p_352_);
v___x_368_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_367_, v_e_353_, v___y_361_);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v___x_368_, 0);
lean_dec(v_unused_377_);
v___x_370_ = v___x_368_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_dec(v___x_368_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_box(v___x_351_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object* v___x_378_, lean_object* v_p_379_, lean_object* v_e_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
uint8_t v___x_214974__boxed_392_; lean_object* v_res_393_; 
v___x_214974__boxed_392_ = lean_unbox(v___x_378_);
v_res_393_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_214974__boxed_392_, v_p_379_, v_e_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec(v___y_381_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(lean_object* v_msgData_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; lean_object* v_env_401_; lean_object* v___x_402_; lean_object* v_mctx_403_; lean_object* v_lctx_404_; lean_object* v_options_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_400_ = lean_st_ref_get(v___y_398_);
v_env_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc_ref(v_env_401_);
lean_dec(v___x_400_);
v___x_402_ = lean_st_ref_get(v___y_396_);
v_mctx_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc_ref(v_mctx_403_);
lean_dec(v___x_402_);
v_lctx_404_ = lean_ctor_get(v___y_395_, 2);
v_options_405_ = lean_ctor_get(v___y_397_, 2);
lean_inc_ref(v_options_405_);
lean_inc_ref(v_lctx_404_);
v___x_406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_406_, 0, v_env_401_);
lean_ctor_set(v___x_406_, 1, v_mctx_403_);
lean_ctor_set(v___x_406_, 2, v_lctx_404_);
lean_ctor_set(v___x_406_, 3, v_options_405_);
v___x_407_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_msgData_394_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6___boxed(lean_object* v_msgData_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msgData_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_416_; double v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = lean_float_of_nat(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object* v_cls_421_, lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_ref_428_; lean_object* v___x_429_; lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_474_; 
v_ref_428_ = lean_ctor_get(v___y_425_, 5);
v___x_429_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_474_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_474_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_474_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v_traceState_435_; lean_object* v_env_436_; lean_object* v_nextMacroScope_437_; lean_object* v_ngen_438_; lean_object* v_auxDeclNGen_439_; lean_object* v_cache_440_; lean_object* v_messages_441_; lean_object* v_infoState_442_; lean_object* v_snapshotTasks_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_473_; 
v___x_434_ = lean_st_ref_take(v___y_426_);
v_traceState_435_ = lean_ctor_get(v___x_434_, 4);
v_env_436_ = lean_ctor_get(v___x_434_, 0);
v_nextMacroScope_437_ = lean_ctor_get(v___x_434_, 1);
v_ngen_438_ = lean_ctor_get(v___x_434_, 2);
v_auxDeclNGen_439_ = lean_ctor_get(v___x_434_, 3);
v_cache_440_ = lean_ctor_get(v___x_434_, 5);
v_messages_441_ = lean_ctor_get(v___x_434_, 6);
v_infoState_442_ = lean_ctor_get(v___x_434_, 7);
v_snapshotTasks_443_ = lean_ctor_get(v___x_434_, 8);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_473_ == 0)
{
v___x_445_ = v___x_434_;
v_isShared_446_ = v_isSharedCheck_473_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snapshotTasks_443_);
lean_inc(v_infoState_442_);
lean_inc(v_messages_441_);
lean_inc(v_cache_440_);
lean_inc(v_traceState_435_);
lean_inc(v_auxDeclNGen_439_);
lean_inc(v_ngen_438_);
lean_inc(v_nextMacroScope_437_);
lean_inc(v_env_436_);
lean_dec(v___x_434_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_473_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
uint64_t v_tid_447_; lean_object* v_traces_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_472_; 
v_tid_447_ = lean_ctor_get_uint64(v_traceState_435_, sizeof(void*)*1);
v_traces_448_ = lean_ctor_get(v_traceState_435_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_traceState_435_);
if (v_isSharedCheck_472_ == 0)
{
v___x_450_ = v_traceState_435_;
v_isShared_451_ = v_isSharedCheck_472_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_traces_448_);
lean_dec(v_traceState_435_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_472_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; double v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_452_ = lean_box(0);
v___x_453_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0);
v___x_454_ = 0;
v___x_455_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
v___x_456_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_456_, 0, v_cls_421_);
lean_ctor_set(v___x_456_, 1, v___x_452_);
lean_ctor_set(v___x_456_, 2, v___x_455_);
lean_ctor_set_float(v___x_456_, sizeof(void*)*3, v___x_453_);
lean_ctor_set_float(v___x_456_, sizeof(void*)*3 + 8, v___x_453_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*3 + 16, v___x_454_);
v___x_457_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2));
v___x_458_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v_a_430_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
lean_inc(v_ref_428_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_ref_428_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_PersistentArray_push___redArg(v_traces_448_, v___x_459_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_460_);
v___x_462_ = v___x_450_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_460_);
lean_ctor_set_uint64(v_reuseFailAlloc_471_, sizeof(void*)*1, v_tid_447_);
v___x_462_ = v_reuseFailAlloc_471_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 4, v___x_462_);
v___x_464_ = v___x_445_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_env_436_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_nextMacroScope_437_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_ngen_438_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_auxDeclNGen_439_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_470_, 5, v_cache_440_);
lean_ctor_set(v_reuseFailAlloc_470_, 6, v_messages_441_);
lean_ctor_set(v_reuseFailAlloc_470_, 7, v_infoState_442_);
lean_ctor_set(v_reuseFailAlloc_470_, 8, v_snapshotTasks_443_);
v___x_464_ = v_reuseFailAlloc_470_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = lean_st_ref_set(v___y_426_, v___x_464_);
v___x_466_ = lean_box(0);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_466_);
v___x_468_ = v___x_432_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object* v_cls_475_, lean_object* v_msg_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_475_, v_msg_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_keys_483_, lean_object* v_i_484_, lean_object* v_k_485_){
_start:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_array_get_size(v_keys_483_);
v___x_487_ = lean_nat_dec_lt(v_i_484_, v___x_486_);
if (v___x_487_ == 0)
{
lean_dec(v_i_484_);
return v___x_487_;
}
else
{
lean_object* v_k_x27_488_; uint8_t v___x_489_; 
v_k_x27_488_ = lean_array_fget_borrowed(v_keys_483_, v_i_484_);
v___x_489_ = l_Lean_instBEqMVarId_beq(v_k_485_, v_k_x27_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_i_484_, v___x_490_);
lean_dec(v_i_484_);
v_i_484_ = v___x_491_;
goto _start;
}
else
{
lean_dec(v_i_484_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_keys_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_493_, v_i_494_, v_k_495_);
lean_dec(v_k_495_);
lean_dec_ref(v_keys_493_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(lean_object* v_x_498_, size_t v_x_499_, lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v_es_501_; lean_object* v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v_j_506_; lean_object* v___x_507_; 
v_es_501_ = lean_ctor_get(v_x_498_, 0);
v___x_502_ = lean_box(2);
v___x_503_ = ((size_t)5ULL);
v___x_504_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_505_ = lean_usize_land(v_x_499_, v___x_504_);
v_j_506_ = lean_usize_to_nat(v___x_505_);
v___x_507_ = lean_array_get_borrowed(v___x_502_, v_es_501_, v_j_506_);
lean_dec(v_j_506_);
switch(lean_obj_tag(v___x_507_))
{
case 0:
{
lean_object* v_key_508_; uint8_t v___x_509_; 
v_key_508_ = lean_ctor_get(v___x_507_, 0);
v___x_509_ = l_Lean_instBEqMVarId_beq(v_x_500_, v_key_508_);
return v___x_509_;
}
case 1:
{
lean_object* v_node_510_; size_t v___x_511_; 
v_node_510_ = lean_ctor_get(v___x_507_, 0);
v___x_511_ = lean_usize_shift_right(v_x_499_, v___x_503_);
v_x_498_ = v_node_510_;
v_x_499_ = v___x_511_;
goto _start;
}
default: 
{
uint8_t v___x_513_; 
v___x_513_ = 0;
return v___x_513_;
}
}
}
else
{
lean_object* v_ks_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_ks_514_ = lean_ctor_get(v_x_498_, 0);
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_ks_514_, v___x_515_, v_x_500_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
size_t v_x_215183__boxed_520_; uint8_t v_res_521_; lean_object* v_r_522_; 
v_x_215183__boxed_520_ = lean_unbox_usize(v_x_518_);
lean_dec(v_x_518_);
v_res_521_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_517_, v_x_215183__boxed_520_, v_x_519_);
lean_dec(v_x_519_);
lean_dec_ref(v_x_517_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
uint64_t v___x_525_; size_t v___x_526_; uint8_t v___x_527_; 
v___x_525_ = l_Lean_instHashableMVarId_hash(v_x_524_);
v___x_526_ = lean_uint64_to_usize(v___x_525_);
v___x_527_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_523_, v___x_526_, v_x_524_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_528_, v_x_529_);
lean_dec(v_x_529_);
lean_dec_ref(v_x_528_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object* v_mvarId_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_mctx_536_; lean_object* v_eAssignment_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_535_ = lean_st_ref_get(v___y_533_);
v_mctx_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_mctx_536_);
lean_dec(v___x_535_);
v_eAssignment_537_ = lean_ctor_get(v_mctx_536_, 8);
lean_inc_ref(v_eAssignment_537_);
lean_dec_ref(v_mctx_536_);
v___x_538_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_537_, v_mvarId_532_);
lean_dec_ref(v_eAssignment_537_);
v___x_539_ = lean_box(v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object* v_mvarId_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec(v_mvarId_541_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object* v_as_545_, size_t v_i_546_, size_t v_stop_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_a_561_; uint8_t v___x_565_; 
v___x_565_ = lean_usize_dec_eq(v_i_546_, v_stop_547_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_566_ = lean_array_uget_borrowed(v_as_545_, v_i_546_);
v___x_569_ = l_Lean_Expr_mvarId_x21(v___x_566_);
v___x_570_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_569_, v___y_556_);
lean_dec(v___x_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; uint8_t v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_570_);
v___x_572_ = lean_unbox(v_a_571_);
lean_dec(v_a_571_);
if (v___x_572_ == 0)
{
goto v___jp_567_;
}
else
{
v_a_561_ = v_b_548_;
goto v___jp_560_;
}
}
else
{
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_573_; uint8_t v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_573_);
lean_dec_ref(v___x_570_);
v___x_574_ = lean_unbox(v_a_573_);
lean_dec(v_a_573_);
if (v___x_574_ == 0)
{
v_a_561_ = v_b_548_;
goto v___jp_560_;
}
else
{
goto v___jp_567_;
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref(v_b_548_);
v_a_575_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_570_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_570_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
v___jp_567_:
{
lean_object* v___x_568_; 
lean_inc(v___x_566_);
v___x_568_ = lean_array_push(v_b_548_, v___x_566_);
v_a_561_ = v___x_568_;
goto v___jp_560_;
}
}
else
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_b_548_);
return v___x_583_;
}
v___jp_560_:
{
size_t v___x_562_; size_t v___x_563_; 
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_add(v_i_546_, v___x_562_);
v_i_546_ = v___x_563_;
v_b_548_ = v_a_561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object* v_as_584_, lean_object* v_i_585_, lean_object* v_stop_586_, lean_object* v_b_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
size_t v_i_boxed_599_; size_t v_stop_boxed_600_; lean_object* v_res_601_; 
v_i_boxed_599_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_stop_boxed_600_ = lean_unbox_usize(v_stop_586_);
lean_dec(v_stop_586_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_584_, v_i_boxed_599_, v_stop_boxed_600_, v_b_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v_as_584_);
return v_res_601_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1));
v___x_606_ = l_Lean_stringToMessageData(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object* v___x_610_, lean_object* v_e_611_, lean_object* v_as_612_, size_t v_sz_613_, size_t v_i_614_, lean_object* v_b_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_a_628_; uint8_t v___x_632_; 
v___x_632_ = lean_usize_dec_lt(v_i_614_, v_sz_613_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec_ref(v_e_611_);
lean_dec(v___x_610_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_b_615_);
return v___x_633_;
}
else
{
lean_object* v_snd_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_740_; 
v_snd_634_ = lean_ctor_get(v_b_615_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_b_615_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_b_615_, 0);
lean_dec(v_unused_741_);
v___x_636_ = v_b_615_;
v_isShared_637_ = v_isSharedCheck_740_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_snd_634_);
lean_dec(v_b_615_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_740_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_array_638_; lean_object* v_start_639_; lean_object* v_stop_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_array_638_ = lean_ctor_get(v_snd_634_, 0);
v_start_639_ = lean_ctor_get(v_snd_634_, 1);
v_stop_640_ = lean_ctor_get(v_snd_634_, 2);
v___x_641_ = lean_box(0);
v___x_642_ = lean_nat_dec_lt(v_start_639_, v_stop_640_);
if (v___x_642_ == 0)
{
lean_object* v___x_644_; 
lean_dec_ref(v_e_611_);
lean_dec(v___x_610_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_641_);
v___x_644_ = v___x_636_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_snd_634_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
else
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_736_; 
lean_inc(v_stop_640_);
lean_inc(v_start_639_);
lean_inc_ref(v_array_638_);
v_isSharedCheck_736_ = !lean_is_exclusive(v_snd_634_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; lean_object* v_unused_738_; lean_object* v_unused_739_; 
v_unused_737_ = lean_ctor_get(v_snd_634_, 2);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_snd_634_, 1);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_snd_634_, 0);
lean_dec(v_unused_739_);
v___x_648_ = v_snd_634_;
v_isShared_649_ = v_isSharedCheck_736_;
goto v_resetjp_647_;
}
else
{
lean_dec(v_snd_634_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_736_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_a_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_650_ = lean_array_uget_borrowed(v_as_612_, v_i_614_);
v___x_651_ = l_Lean_Expr_mvarId_x21(v_a_650_);
v___x_652_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_651_, v___y_623_);
lean_dec(v___x_651_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_727_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_727_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_727_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_727_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_657_ = lean_array_fget(v_array_638_, v_start_639_);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_nat_add(v_start_639_, v___x_658_);
lean_dec(v_start_639_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_659_);
v___x_661_ = v___x_648_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_array_638_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_stop_640_);
v___x_661_ = v_reuseFailAlloc_726_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
uint8_t v___y_673_; uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_unbox(v___x_657_);
lean_dec(v___x_657_);
v___x_724_ = l_Lean_BinderInfo_isInstImplicit(v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v_a_653_);
v___y_673_ = v___x_724_;
goto v___jp_672_;
}
else
{
uint8_t v___x_725_; 
v___x_725_ = lean_unbox(v_a_653_);
lean_dec(v_a_653_);
if (v___x_725_ == 0)
{
v___y_673_ = v___x_724_;
goto v___jp_672_;
}
else
{
lean_del_object(v___x_655_);
lean_del_object(v___x_636_);
goto v___jp_670_;
}
}
v___jp_662_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0));
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_661_);
lean_ctor_set(v___x_636_, 0, v___x_663_);
v___x_665_ = v___x_636_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_661_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_665_);
v___x_667_ = v___x_655_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
v___jp_670_:
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_641_);
lean_ctor_set(v___x_671_, 1, v___x_661_);
v_a_628_ = v___x_671_;
goto v___jp_627_;
}
v___jp_672_:
{
if (v___y_673_ == 0)
{
lean_del_object(v___x_655_);
lean_del_object(v___x_636_);
goto v___jp_670_;
}
else
{
lean_object* v___x_674_; 
lean_inc(v___y_625_);
lean_inc_ref(v___y_624_);
lean_inc(v___y_623_);
lean_inc_ref(v___y_622_);
lean_inc(v_a_650_);
v___x_674_ = lean_infer_type(v_a_650_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref(v___x_674_);
lean_inc(v_a_650_);
v___x_676_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_a_650_, v_a_675_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; uint8_t v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_676_);
v___x_678_ = lean_unbox(v_a_677_);
lean_dec(v_a_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_620_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; uint8_t v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref(v___x_679_);
v___x_681_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
if (v___x_681_ == 0)
{
lean_dec_ref(v_e_611_);
lean_dec(v___x_610_);
goto v___jp_662_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
v___x_683_ = l_Lean_MessageData_ofName(v___x_610_);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Lean_indentExpr(v_e_611_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_Meta_Sym_reportIssue(v___x_688_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_dec_ref(v___x_689_);
goto v___jp_662_;
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v___x_661_);
lean_del_object(v___x_655_);
lean_del_object(v___x_636_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v___x_661_);
lean_del_object(v___x_655_);
lean_del_object(v___x_636_);
lean_dec_ref(v_e_611_);
lean_dec(v___x_610_);
v_a_698_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_679_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_679_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v___x_706_; 
lean_del_object(v___x_655_);
lean_del_object(v___x_636_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_641_);
lean_ctor_set(v___x_706_, 1, v___x_661_);
v_a_628_ = v___x_706_;
goto v___jp_627_;
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v___x_661_);
lean_del_object(v___x_655_);
lean_del_object(v___x_636_);
lean_dec_ref(v_e_611_);
lean_dec(v___x_610_);
v_a_707_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_676_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_676_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
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
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v___x_661_);
lean_del_object(v___x_655_);
lean_del_object(v___x_636_);
lean_dec_ref(v_e_611_);
lean_dec(v___x_610_);
v_a_715_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_674_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_674_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
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
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_del_object(v___x_648_);
lean_dec(v_stop_640_);
lean_dec(v_start_639_);
lean_dec_ref(v_array_638_);
lean_del_object(v___x_636_);
lean_dec_ref(v_e_611_);
lean_dec(v___x_610_);
v_a_728_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_652_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_652_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
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
}
}
}
v___jp_627_:
{
size_t v___x_629_; size_t v___x_630_; 
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_614_, v___x_629_);
v_i_614_ = v___x_630_;
v_b_615_ = v_a_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object** _args){
lean_object* v___x_742_ = _args[0];
lean_object* v_e_743_ = _args[1];
lean_object* v_as_744_ = _args[2];
lean_object* v_sz_745_ = _args[3];
lean_object* v_i_746_ = _args[4];
lean_object* v_b_747_ = _args[5];
lean_object* v___y_748_ = _args[6];
lean_object* v___y_749_ = _args[7];
lean_object* v___y_750_ = _args[8];
lean_object* v___y_751_ = _args[9];
lean_object* v___y_752_ = _args[10];
lean_object* v___y_753_ = _args[11];
lean_object* v___y_754_ = _args[12];
lean_object* v___y_755_ = _args[13];
lean_object* v___y_756_ = _args[14];
lean_object* v___y_757_ = _args[15];
lean_object* v___y_758_ = _args[16];
_start:
{
size_t v_sz_boxed_759_; size_t v_i_boxed_760_; lean_object* v_res_761_; 
v_sz_boxed_759_ = lean_unbox_usize(v_sz_745_);
lean_dec(v_sz_745_);
v_i_boxed_760_ = lean_unbox_usize(v_i_746_);
lean_dec(v_i_746_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_742_, v_e_743_, v_as_744_, v_sz_boxed_759_, v_i_boxed_760_, v_b_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v_as_744_);
return v_res_761_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_774_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6));
v___x_775_ = l_Lean_Name_append(v___x_774_, v___x_773_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18));
v___x_796_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17));
v___x_797_ = l_Lean_mkConst(v___x_796_, v___x_795_);
return v___x_797_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21(void){
_start:
{
uint8_t v___x_800_; uint64_t v___x_801_; 
v___x_800_ = 1;
v___x_801_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object* v_e_802_, lean_object* v_thm_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_802_, v___y_804_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___x_827_);
v___x_829_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_806_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_1169_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_1169_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_1169_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
uint8_t v___x_834_; 
v___x_834_ = lean_nat_dec_lt(v_a_828_, v_a_830_);
lean_dec(v_a_830_);
lean_dec(v_a_828_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_dec_ref(v_thm_803_);
lean_dec_ref(v_e_802_);
v___x_835_ = lean_box(0);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_835_);
v___x_837_ = v___x_832_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
lean_object* v___x_839_; uint8_t v___x_840_; 
lean_del_object(v___x_832_);
lean_inc_ref(v_e_802_);
v___x_839_ = l_Lean_Expr_cleanupAnnotations(v_e_802_);
v___x_840_ = l_Lean_Expr_isApp(v___x_839_);
if (v___x_840_ == 0)
{
lean_dec_ref(v___x_839_);
lean_dec_ref(v_thm_803_);
lean_dec_ref(v_e_802_);
goto v___jp_824_;
}
else
{
lean_object* v_arg_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_arg_841_ = lean_ctor_get(v___x_839_, 1);
lean_inc_ref(v_arg_841_);
v___x_842_ = l_Lean_Expr_appFnCleanup___redArg(v___x_839_);
v___x_843_ = l_Lean_Expr_isApp(v___x_842_);
if (v___x_843_ == 0)
{
lean_dec_ref(v___x_842_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_thm_803_);
lean_dec_ref(v_e_802_);
goto v___jp_824_;
}
else
{
lean_object* v_arg_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_arg_844_ = lean_ctor_get(v___x_842_, 1);
lean_inc_ref(v_arg_844_);
v___x_845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_842_);
v___x_846_ = l_Lean_Expr_isApp(v___x_845_);
if (v___x_846_ == 0)
{
lean_dec_ref(v___x_845_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_thm_803_);
lean_dec_ref(v_e_802_);
goto v___jp_824_;
}
else
{
lean_object* v_arg_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_arg_847_ = lean_ctor_get(v___x_845_, 1);
lean_inc_ref(v_arg_847_);
v___x_848_ = l_Lean_Expr_appFnCleanup___redArg(v___x_845_);
v___x_849_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1));
v___x_850_ = l_Lean_Expr_isConstOf(v___x_848_, v___x_849_);
lean_dec_ref(v___x_848_);
if (v___x_850_ == 0)
{
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_thm_803_);
lean_dec_ref(v_e_802_);
goto v___jp_824_;
}
else
{
lean_object* v_declName_851_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_880_; lean_object* v___y_881_; uint8_t v___y_882_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v_a_919_; lean_object* v___y_947_; uint8_t v___y_948_; lean_object* v___y_949_; lean_object* v___y_960_; lean_object* v___x_984_; 
v_declName_851_ = lean_ctor_get(v_thm_803_, 0);
lean_inc_n(v_declName_851_, 2);
lean_dec_ref(v_thm_803_);
v___x_984_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_851_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; uint8_t v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v_a_1062_; lean_object* v___x_1093_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc_n(v_a_985_, 2);
lean_dec_ref(v___x_984_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
v___x_1093_ = lean_infer_type(v_a_985_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; uint8_t v_foApprox_1096_; uint8_t v_ctxApprox_1097_; uint8_t v_quasiPatternApprox_1098_; uint8_t v_constApprox_1099_; uint8_t v_isDefEqStuckEx_1100_; uint8_t v_unificationHints_1101_; uint8_t v_proofIrrelevance_1102_; uint8_t v_assignSyntheticOpaque_1103_; uint8_t v_offsetCnstrs_1104_; uint8_t v_etaStruct_1105_; uint8_t v_univApprox_1106_; uint8_t v_iota_1107_; uint8_t v_beta_1108_; uint8_t v_proj_1109_; uint8_t v_zeta_1110_; uint8_t v_zetaDelta_1111_; uint8_t v_zetaUnused_1112_; uint8_t v_zetaHave_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1152_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l_Lean_Meta_Context_config(v___y_810_);
v_foApprox_1096_ = lean_ctor_get_uint8(v___x_1095_, 0);
v_ctxApprox_1097_ = lean_ctor_get_uint8(v___x_1095_, 1);
v_quasiPatternApprox_1098_ = lean_ctor_get_uint8(v___x_1095_, 2);
v_constApprox_1099_ = lean_ctor_get_uint8(v___x_1095_, 3);
v_isDefEqStuckEx_1100_ = lean_ctor_get_uint8(v___x_1095_, 4);
v_unificationHints_1101_ = lean_ctor_get_uint8(v___x_1095_, 5);
v_proofIrrelevance_1102_ = lean_ctor_get_uint8(v___x_1095_, 6);
v_assignSyntheticOpaque_1103_ = lean_ctor_get_uint8(v___x_1095_, 7);
v_offsetCnstrs_1104_ = lean_ctor_get_uint8(v___x_1095_, 8);
v_etaStruct_1105_ = lean_ctor_get_uint8(v___x_1095_, 10);
v_univApprox_1106_ = lean_ctor_get_uint8(v___x_1095_, 11);
v_iota_1107_ = lean_ctor_get_uint8(v___x_1095_, 12);
v_beta_1108_ = lean_ctor_get_uint8(v___x_1095_, 13);
v_proj_1109_ = lean_ctor_get_uint8(v___x_1095_, 14);
v_zeta_1110_ = lean_ctor_get_uint8(v___x_1095_, 15);
v_zetaDelta_1111_ = lean_ctor_get_uint8(v___x_1095_, 16);
v_zetaUnused_1112_ = lean_ctor_get_uint8(v___x_1095_, 17);
v_zetaHave_1113_ = lean_ctor_get_uint8(v___x_1095_, 18);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1115_ = v___x_1095_;
v_isShared_1116_ = v_isSharedCheck_1152_;
goto v_resetjp_1114_;
}
else
{
lean_dec(v___x_1095_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1152_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v_trackZetaDelta_1117_; lean_object* v_zetaDeltaSet_1118_; lean_object* v_lctx_1119_; lean_object* v_localInstances_1120_; lean_object* v_defEqCtx_x3f_1121_; lean_object* v_synthPendingDepth_1122_; lean_object* v_canUnfold_x3f_1123_; uint8_t v_univApprox_1124_; uint8_t v_inTypeClassResolution_1125_; uint8_t v_cacheInferType_1126_; uint8_t v___x_1127_; lean_object* v_config_1129_; 
v_trackZetaDelta_1117_ = lean_ctor_get_uint8(v___y_810_, sizeof(void*)*7);
v_zetaDeltaSet_1118_ = lean_ctor_get(v___y_810_, 1);
v_lctx_1119_ = lean_ctor_get(v___y_810_, 2);
v_localInstances_1120_ = lean_ctor_get(v___y_810_, 3);
v_defEqCtx_x3f_1121_ = lean_ctor_get(v___y_810_, 4);
v_synthPendingDepth_1122_ = lean_ctor_get(v___y_810_, 5);
v_canUnfold_x3f_1123_ = lean_ctor_get(v___y_810_, 6);
v_univApprox_1124_ = lean_ctor_get_uint8(v___y_810_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1125_ = lean_ctor_get_uint8(v___y_810_, sizeof(void*)*7 + 2);
v_cacheInferType_1126_ = lean_ctor_get_uint8(v___y_810_, sizeof(void*)*7 + 3);
v___x_1127_ = 1;
if (v_isShared_1116_ == 0)
{
v_config_1129_ = v___x_1115_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 0, v_foApprox_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 1, v_ctxApprox_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 2, v_quasiPatternApprox_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 3, v_constApprox_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 4, v_isDefEqStuckEx_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 5, v_unificationHints_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 6, v_proofIrrelevance_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 7, v_assignSyntheticOpaque_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 8, v_offsetCnstrs_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 10, v_etaStruct_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 11, v_univApprox_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 12, v_iota_1107_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 13, v_beta_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 14, v_proj_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 15, v_zeta_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 16, v_zetaDelta_1111_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 17, v_zetaUnused_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, 18, v_zetaHave_1113_);
v_config_1129_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
uint64_t v___x_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; uint64_t v___x_1135_; uint64_t v___x_1136_; uint64_t v_key_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_ctor_set_uint8(v_config_1129_, 9, v___x_1127_);
v___x_1130_ = l_Lean_Meta_Context_configKey(v___y_810_);
v___x_1131_ = 2ULL;
v___x_1132_ = lean_uint64_shift_right(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_box(0);
v___x_1134_ = 0;
v___x_1135_ = lean_uint64_shift_left(v___x_1132_, v___x_1131_);
v___x_1136_ = lean_uint64_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21);
v_key_1137_ = lean_uint64_lor(v___x_1135_, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1138_, 0, v_config_1129_);
lean_ctor_set_uint64(v___x_1138_, sizeof(void*)*1, v_key_1137_);
lean_inc(v_canUnfold_x3f_1123_);
lean_inc(v_synthPendingDepth_1122_);
lean_inc(v_defEqCtx_x3f_1121_);
lean_inc_ref(v_localInstances_1120_);
lean_inc_ref(v_lctx_1119_);
lean_inc(v_zetaDeltaSet_1118_);
v___x_1139_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v_zetaDeltaSet_1118_);
lean_ctor_set(v___x_1139_, 2, v_lctx_1119_);
lean_ctor_set(v___x_1139_, 3, v_localInstances_1120_);
lean_ctor_set(v___x_1139_, 4, v_defEqCtx_x3f_1121_);
lean_ctor_set(v___x_1139_, 5, v_synthPendingDepth_1122_);
lean_ctor_set(v___x_1139_, 6, v_canUnfold_x3f_1123_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*7, v_trackZetaDelta_1117_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*7 + 1, v_univApprox_1124_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1125_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*7 + 3, v_cacheInferType_1126_);
v___x_1140_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1094_, v___x_1133_, v___x_1134_, v___x_1139_, v___y_811_, v___y_812_, v___y_813_);
lean_dec_ref(v___x_1139_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v___x_1140_);
v_a_1062_ = v_a_1141_;
goto v___jp_1061_;
}
else
{
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1142_; 
v_a_1142_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1142_);
lean_dec_ref(v___x_1140_);
v_a_1062_ = v_a_1142_;
goto v___jp_1061_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_e_802_);
v_a_1143_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1140_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1140_);
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
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_e_802_);
v_a_1153_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1093_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1093_);
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
v___jp_986_:
{
if (lean_obj_tag(v___y_991_) == 0)
{
lean_object* v_a_992_; uint8_t v___x_993_; 
v_a_992_ = lean_ctor_get(v___y_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v___y_991_);
v___x_993_ = lean_unbox(v_a_992_);
lean_dec(v_a_992_);
if (v___x_993_ == 0)
{
lean_dec_ref(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v_a_985_);
v___y_960_ = v___y_990_;
goto v___jp_959_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; size_t v_sz_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
lean_dec_ref(v___y_990_);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_array_get_size(v___y_989_);
v___x_996_ = l_Array_toSubarray___redArg(v___y_989_, v___x_994_, v___x_995_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_996_);
v_sz_999_ = lean_array_size(v___y_988_);
v___x_1000_ = ((size_t)0ULL);
lean_inc_ref(v_e_802_);
lean_inc(v_declName_851_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_851_, v_e_802_, v___y_988_, v_sz_999_, v___x_1000_, v___x_998_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1044_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1044_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1044_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_fst_1006_; 
v_fst_1006_ = lean_ctor_get(v_a_1002_, 0);
lean_inc(v_fst_1006_);
lean_dec(v_a_1002_);
if (lean_obj_tag(v_fst_1006_) == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_a_1009_; lean_object* v___x_1010_; 
lean_del_object(v___x_1004_);
v___x_1007_ = l_Lean_mkAppN(v_a_985_, v___y_988_);
v___x_1008_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_1007_, v___y_811_);
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
lean_inc_ref(v_e_802_);
v___x_1010_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_802_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_808_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19);
lean_inc_ref(v_e_802_);
v___x_1015_ = l_Lean_mkApp4(v___x_1014_, v_e_802_, v_a_1013_, v_a_1011_, v_a_1009_);
v___x_1016_ = lean_array_get_size(v___y_988_);
v___x_1017_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20));
v___x_1018_ = lean_nat_dec_lt(v___x_994_, v___x_1016_);
if (v___x_1018_ == 0)
{
lean_dec_ref(v___y_988_);
v___y_917_ = v___x_1015_;
v___y_918_ = v___y_987_;
v_a_919_ = v___x_1017_;
goto v___jp_916_;
}
else
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_le(v___x_1016_, v___x_1016_);
if (v___x_1019_ == 0)
{
if (v___x_1018_ == 0)
{
lean_dec_ref(v___y_988_);
v___y_917_ = v___x_1015_;
v___y_918_ = v___y_987_;
v_a_919_ = v___x_1017_;
goto v___jp_916_;
}
else
{
size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_usize_of_nat(v___x_1016_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_988_, v___x_1000_, v___x_1020_, v___x_1017_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec_ref(v___y_988_);
v___y_947_ = v___x_1015_;
v___y_948_ = v___y_987_;
v___y_949_ = v___x_1021_;
goto v___jp_946_;
}
}
else
{
size_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_usize_of_nat(v___x_1016_);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_988_, v___x_1000_, v___x_1022_, v___x_1017_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec_ref(v___y_988_);
v___y_947_ = v___x_1015_;
v___y_948_ = v___y_987_;
v___y_949_ = v___x_1023_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_a_1011_);
lean_dec(v_a_1009_);
lean_dec_ref(v___y_988_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_1024_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1012_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1012_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_a_1009_);
lean_dec_ref(v___y_988_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_1032_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1010_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1010_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1042_; 
lean_dec_ref(v___y_988_);
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_val_1040_ = lean_ctor_get(v_fst_1006_, 0);
lean_inc(v_val_1040_);
lean_dec_ref(v_fst_1006_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_val_1040_);
v___x_1042_ = v___x_1004_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_val_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v___y_988_);
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_1045_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1001_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1001_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_1053_ = lean_ctor_get(v___y_991_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___y_991_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___y_991_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___y_991_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
v___jp_1061_:
{
lean_object* v_snd_1063_; lean_object* v_fst_1064_; lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_snd_1063_ = lean_ctor_get(v_a_1062_, 1);
lean_inc(v_snd_1063_);
v_fst_1064_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_fst_1064_);
lean_dec_ref(v_a_1062_);
v_fst_1065_ = lean_ctor_get(v_snd_1063_, 0);
lean_inc(v_fst_1065_);
v_snd_1066_ = lean_ctor_get(v_snd_1063_, 1);
lean_inc_n(v_snd_1066_, 2);
lean_dec(v_snd_1063_);
v___x_1067_ = l_Lean_Expr_cleanupAnnotations(v_snd_1066_);
v___x_1068_ = l_Lean_Expr_isApp(v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec_ref(v___x_1067_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_e_802_);
goto v___jp_821_;
}
else
{
lean_object* v_arg_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_arg_1069_ = lean_ctor_get(v___x_1067_, 1);
lean_inc_ref(v_arg_1069_);
v___x_1070_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1067_);
v___x_1071_ = l_Lean_Expr_isApp(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v___x_1070_);
lean_dec_ref(v_arg_1069_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_e_802_);
goto v___jp_821_;
}
else
{
lean_object* v_arg_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_arg_1072_ = lean_ctor_get(v___x_1070_, 1);
lean_inc_ref(v_arg_1072_);
v___x_1073_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1070_);
v___x_1074_ = l_Lean_Expr_isApp(v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v___x_1073_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_arg_1069_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_e_802_);
goto v___jp_821_;
}
else
{
lean_object* v_arg_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_arg_1075_ = lean_ctor_get(v___x_1073_, 1);
lean_inc_ref(v_arg_1075_);
v___x_1076_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1073_);
v___x_1077_ = l_Lean_Expr_isConstOf(v___x_1076_, v___x_849_);
lean_dec_ref(v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_arg_1069_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_e_802_);
goto v___jp_821_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_isExprDefEq(v_arg_847_, v_arg_1075_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; uint8_t v___x_1080_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
v___x_1080_ = lean_unbox(v_a_1079_);
lean_dec(v_a_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_arg_1069_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
v___y_987_ = v___x_1077_;
v___y_988_ = v_fst_1064_;
v___y_989_ = v_fst_1065_;
v___y_990_ = v_snd_1066_;
v___y_991_ = v___x_1078_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1081_; 
lean_dec_ref(v___x_1078_);
v___x_1081_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1077_, v_arg_1072_, v_arg_844_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; uint8_t v___x_1083_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = lean_unbox(v_a_1082_);
lean_dec(v_a_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v_arg_1069_);
lean_dec(v_fst_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_a_985_);
lean_dec_ref(v_arg_841_);
v___y_960_ = v_snd_1066_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1077_, v_arg_1069_, v_arg_841_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
v___y_987_ = v___x_1077_;
v___y_988_ = v_fst_1064_;
v___y_989_ = v_fst_1065_;
v___y_990_ = v_snd_1066_;
v___y_991_ = v___x_1084_;
goto v___jp_986_;
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v_arg_1069_);
lean_dec(v_snd_1066_);
lean_dec(v_fst_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_a_985_);
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_e_802_);
v_a_1085_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1081_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1081_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_arg_1069_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
v___y_987_ = v___x_1077_;
v___y_988_ = v_fst_1064_;
v___y_989_ = v_fst_1065_;
v___y_990_ = v_snd_1066_;
v___y_991_ = v___x_1078_;
goto v___jp_986_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_e_802_);
v_a_1161_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_984_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_984_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
v___jp_852_:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_802_, v___y_855_);
lean_dec_ref(v_e_802_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_865_);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_a_866_, v___x_867_);
lean_dec(v_a_866_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v_declName_851_);
v___x_870_ = l_Lean_Meta_Grind_addNewRawFact(v___y_853_, v___y_854_, v___x_868_, v___x_869_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
return v___x_870_;
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v_declName_851_);
v_a_871_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_865_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_865_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
v___jp_879_:
{
if (v___y_882_ == 0)
{
lean_object* v_options_883_; uint8_t v_hasTrace_884_; 
v_options_883_ = lean_ctor_get(v___y_812_, 2);
v_hasTrace_884_ = lean_ctor_get_uint8(v_options_883_, sizeof(void*)*1);
if (v_hasTrace_884_ == 0)
{
v___y_853_ = v___y_880_;
v___y_854_ = v___y_881_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
v___y_864_ = v___y_813_;
goto v___jp_852_;
}
else
{
lean_object* v_inheritedTraceOptions_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_inheritedTraceOptions_885_ = lean_ctor_get(v___y_812_, 13);
v___x_886_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_887_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7);
v___x_888_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_885_, v_options_883_, v___x_887_);
if (v___x_888_ == 0)
{
v___y_853_ = v___y_880_;
v___y_854_ = v___y_881_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
v___y_864_ = v___y_813_;
goto v___jp_852_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_inc(v_declName_851_);
v___x_889_ = l_Lean_MessageData_ofName(v_declName_851_);
v___x_890_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
lean_inc_ref(v___y_881_);
v___x_892_ = l_Lean_MessageData_ofExpr(v___y_881_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_886_, v___x_893_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_dec_ref(v___x_894_);
v___y_853_ = v___y_880_;
v___y_854_ = v___y_881_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
v___y_864_ = v___y_813_;
goto v___jp_852_;
}
else
{
lean_dec_ref(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
return v___x_894_;
}
}
}
}
else
{
lean_object* v___x_895_; 
lean_dec_ref(v___y_881_);
lean_dec_ref(v___y_880_);
v___x_895_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_808_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; uint8_t v___x_897_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref(v___x_895_);
v___x_897_ = lean_unbox(v_a_896_);
lean_dec(v_a_896_);
if (v___x_897_ == 0)
{
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
goto v___jp_815_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_898_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_899_ = l_Lean_MessageData_ofName(v_declName_851_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l_Lean_indentExpr(v_e_802_);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l_Lean_Meta_Sym_reportIssue(v___x_906_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_dec_ref(v___x_907_);
goto v___jp_815_;
}
else
{
return v___x_907_;
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_908_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_895_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_895_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
v___jp_916_:
{
uint8_t v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; 
v___x_920_ = 0;
v___x_921_ = 1;
v___x_922_ = l_Lean_Meta_mkLambdaFVars(v_a_919_, v___y_917_, v___x_920_, v___y_918_, v___x_920_, v___y_918_, v___x_921_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec_ref(v_a_919_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_926_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v___x_922_);
v___x_924_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_923_, v___y_811_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc_n(v_a_925_, 2);
lean_dec_ref(v___x_924_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
v___x_926_ = lean_infer_type(v_a_925_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; uint8_t v___x_928_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = l_Lean_Expr_hasMVar(v_a_925_);
if (v___x_928_ == 0)
{
uint8_t v___x_929_; 
v___x_929_ = l_Lean_Expr_hasMVar(v_a_927_);
v___y_880_ = v_a_925_;
v___y_881_ = v_a_927_;
v___y_882_ = v___x_929_;
goto v___jp_879_;
}
else
{
v___y_880_ = v_a_925_;
v___y_881_ = v_a_927_;
v___y_882_ = v___y_918_;
goto v___jp_879_;
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_a_925_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_930_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_926_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
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
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_938_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_922_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_922_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
v___jp_946_:
{
if (lean_obj_tag(v___y_949_) == 0)
{
lean_object* v_a_950_; 
v_a_950_ = lean_ctor_get(v___y_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v___y_949_);
v___y_917_ = v___y_947_;
v___y_918_ = v___y_948_;
v_a_919_ = v_a_950_;
goto v___jp_916_;
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref(v___y_947_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_951_ = lean_ctor_get(v___y_949_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___y_949_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___y_949_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___y_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
v___jp_959_:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_808_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; uint8_t v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
v___x_963_ = lean_unbox(v_a_962_);
lean_dec(v_a_962_);
if (v___x_963_ == 0)
{
lean_dec_ref(v___y_960_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
goto v___jp_818_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_964_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_965_ = l_Lean_MessageData_ofName(v_declName_851_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_indentExpr(v_e_802_);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Lean_indentExpr(v___y_960_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_Meta_Sym_reportIssue(v___x_974_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_dec_ref(v___x_975_);
goto v___jp_818_;
}
else
{
return v___x_975_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v___y_960_);
lean_dec(v_declName_851_);
lean_dec_ref(v_e_802_);
v_a_976_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_961_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_961_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
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
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_a_828_);
lean_dec_ref(v_thm_803_);
lean_dec_ref(v_e_802_);
v_a_1170_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_829_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_829_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_thm_803_);
lean_dec_ref(v_e_802_);
v_a_1178_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_827_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_827_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
v___jp_815_:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
v___jp_818_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_box(0);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
v___jp_821_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_box(0);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
v___jp_824_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_box(0);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object* v_e_1186_, lean_object* v_thm_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(v_e_1186_, v_thm_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec(v___y_1188_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object* v_thm_1200_, lean_object* v_e_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___f_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed), 13, 2);
lean_closure_set(v___f_1213_, 0, v_e_1201_);
lean_closure_set(v___f_1213_, 1, v_thm_1200_);
v___x_1214_ = 0;
v___x_1215_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v___f_1213_, v___x_1214_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object* v_thm_1216_, lean_object* v_e_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_thm_1216_, v_e_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec(v_a_1218_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object* v_mvarId_1230_, lean_object* v_val_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_1230_, v_val_1231_, v___y_1239_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object* v_mvarId_1244_, lean_object* v_val_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(v_mvarId_1244_, v_val_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object* v_mvarId_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_1258_, v___y_1266_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object* v_mvarId_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(v_mvarId_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v_mvarId_1271_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object* v_cls_1284_, lean_object* v_msg_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_1284_, v_msg_1285_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object* v_cls_1298_, lean_object* v_msg_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(v_cls_1298_, v_msg_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v___y_1300_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_1313_, v_x_1314_, v_x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object* v_00_u03b2_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1318_, v_x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(v_00_u03b2_1321_, v_x_1322_, v_x_1323_);
lean_dec(v_x_1323_);
lean_dec_ref(v_x_1322_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, size_t v_x_1328_, size_t v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1327_, v_x_1328_, v_x_1329_, v_x_1330_, v_x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
size_t v_x_216591__boxed_1339_; size_t v_x_216592__boxed_1340_; lean_object* v_res_1341_; 
v_x_216591__boxed_1339_ = lean_unbox_usize(v_x_1335_);
lean_dec(v_x_1335_);
v_x_216592__boxed_1340_ = lean_unbox_usize(v_x_1336_);
lean_dec(v_x_1336_);
v_res_1341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(v_00_u03b2_1333_, v_x_1334_, v_x_216591__boxed_1339_, v_x_216592__boxed_1340_, v_x_1337_, v_x_1338_);
return v_res_1341_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1342_, lean_object* v_x_1343_, size_t v_x_1344_, lean_object* v_x_1345_){
_start:
{
uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1343_, v_x_1344_, v_x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_){
_start:
{
size_t v_x_216608__boxed_1351_; uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_x_216608__boxed_1351_ = lean_unbox_usize(v_x_1349_);
lean_dec(v_x_1349_);
v_res_1352_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(v_00_u03b2_1347_, v_x_1348_, v_x_216608__boxed_1351_, v_x_1350_);
lean_dec(v_x_1350_);
lean_dec_ref(v_x_1348_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03b2_1354_, lean_object* v_n_1355_, lean_object* v_k_1356_, lean_object* v_v_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_n_1355_, v_k_1356_, v_v_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_1359_, size_t v_depth_1360_, lean_object* v_keys_1361_, lean_object* v_vals_1362_, lean_object* v_heq_1363_, lean_object* v_i_1364_, lean_object* v_entries_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_1360_, v_keys_1361_, v_vals_1362_, v_i_1364_, v_entries_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1367_, lean_object* v_depth_1368_, lean_object* v_keys_1369_, lean_object* v_vals_1370_, lean_object* v_heq_1371_, lean_object* v_i_1372_, lean_object* v_entries_1373_){
_start:
{
size_t v_depth_boxed_1374_; lean_object* v_res_1375_; 
v_depth_boxed_1374_ = lean_unbox_usize(v_depth_1368_);
lean_dec(v_depth_1368_);
v_res_1375_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_1367_, v_depth_boxed_1374_, v_keys_1369_, v_vals_1370_, v_heq_1371_, v_i_1372_, v_entries_1373_);
lean_dec_ref(v_vals_1370_);
lean_dec_ref(v_keys_1369_);
return v_res_1375_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_1376_, lean_object* v_keys_1377_, lean_object* v_vals_1378_, lean_object* v_heq_1379_, lean_object* v_i_1380_, lean_object* v_k_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_1377_, v_i_1380_, v_k_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(lean_object* v_00_u03b2_1383_, lean_object* v_keys_1384_, lean_object* v_vals_1385_, lean_object* v_heq_1386_, lean_object* v_i_1387_, lean_object* v_k_1388_){
_start:
{
uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_res_1389_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(v_00_u03b2_1383_, v_keys_1384_, v_vals_1385_, v_heq_1386_, v_i_1387_, v_k_1388_);
lean_dec(v_k_1388_);
lean_dec_ref(v_vals_1385_);
lean_dec_ref(v_keys_1384_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11(lean_object* v_00_u03b2_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_x_1392_, v_x_1393_, v_x_1394_, v_x_1395_);
return v___x_1396_;
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
