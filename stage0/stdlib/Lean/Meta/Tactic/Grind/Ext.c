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
size_t v_x_214749__boxed_298_; size_t v_x_214750__boxed_299_; lean_object* v_res_300_; 
v_x_214749__boxed_298_ = lean_unbox_usize(v_x_294_);
lean_dec(v_x_294_);
v_x_214750__boxed_299_ = lean_unbox_usize(v_x_295_);
lean_dec(v_x_295_);
v_res_300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_293_, v_x_214749__boxed_298_, v_x_214750__boxed_299_, v_x_296_, v_x_297_);
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
lean_object* v___x_312_; lean_object* v_mctx_313_; lean_object* v_cache_314_; lean_object* v_zetaDeltaFVarIds_315_; lean_object* v_postponed_316_; lean_object* v_diag_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_344_; 
v___x_312_ = lean_st_ref_take(v___y_310_);
v_mctx_313_ = lean_ctor_get(v___x_312_, 0);
v_cache_314_ = lean_ctor_get(v___x_312_, 1);
v_zetaDeltaFVarIds_315_ = lean_ctor_get(v___x_312_, 2);
v_postponed_316_ = lean_ctor_get(v___x_312_, 3);
v_diag_317_ = lean_ctor_get(v___x_312_, 4);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_344_ == 0)
{
v___x_319_ = v___x_312_;
v_isShared_320_ = v_isSharedCheck_344_;
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
v_isShared_320_ = v_isSharedCheck_344_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_depth_321_; lean_object* v_levelAssignDepth_322_; lean_object* v_mvarCounter_323_; lean_object* v_lDepth_324_; lean_object* v_decls_325_; lean_object* v_userNames_326_; lean_object* v_lAssignment_327_; lean_object* v_eAssignment_328_; lean_object* v_dAssignment_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_343_; 
v_depth_321_ = lean_ctor_get(v_mctx_313_, 0);
v_levelAssignDepth_322_ = lean_ctor_get(v_mctx_313_, 1);
v_mvarCounter_323_ = lean_ctor_get(v_mctx_313_, 2);
v_lDepth_324_ = lean_ctor_get(v_mctx_313_, 3);
v_decls_325_ = lean_ctor_get(v_mctx_313_, 4);
v_userNames_326_ = lean_ctor_get(v_mctx_313_, 5);
v_lAssignment_327_ = lean_ctor_get(v_mctx_313_, 6);
v_eAssignment_328_ = lean_ctor_get(v_mctx_313_, 7);
v_dAssignment_329_ = lean_ctor_get(v_mctx_313_, 8);
v_isSharedCheck_343_ = !lean_is_exclusive(v_mctx_313_);
if (v_isSharedCheck_343_ == 0)
{
v___x_331_ = v_mctx_313_;
v_isShared_332_ = v_isSharedCheck_343_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_dAssignment_329_);
lean_inc(v_eAssignment_328_);
lean_inc(v_lAssignment_327_);
lean_inc(v_userNames_326_);
lean_inc(v_decls_325_);
lean_inc(v_lDepth_324_);
lean_inc(v_mvarCounter_323_);
lean_inc(v_levelAssignDepth_322_);
lean_inc(v_depth_321_);
lean_dec(v_mctx_313_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_343_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_eAssignment_328_, v_mvarId_308_, v_val_309_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 7, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_depth_321_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_levelAssignDepth_322_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_mvarCounter_323_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_lDepth_324_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_decls_325_);
lean_ctor_set(v_reuseFailAlloc_342_, 5, v_userNames_326_);
lean_ctor_set(v_reuseFailAlloc_342_, 6, v_lAssignment_327_);
lean_ctor_set(v_reuseFailAlloc_342_, 7, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_342_, 8, v_dAssignment_329_);
v___x_335_ = v_reuseFailAlloc_342_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_335_);
v___x_337_ = v___x_319_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_cache_314_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_zetaDeltaFVarIds_315_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_postponed_316_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_diag_317_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_st_ref_set(v___y_310_, v___x_337_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object* v_mvarId_345_, lean_object* v_val_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_345_, v_val_346_, v___y_347_);
lean_dec(v___y_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(uint8_t v___x_350_, lean_object* v_p_351_, lean_object* v_e_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_Expr_isMVar(v_p_351_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_isExprDefEq(v_p_351_, v_e_352_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v___x_366_ = l_Lean_Expr_mvarId_x21(v_p_351_);
lean_dec_ref(v_p_351_);
v___x_367_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_366_, v_e_352_, v___y_360_);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v___x_367_, 0);
lean_dec(v_unused_376_);
v___x_369_ = v___x_367_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_dec(v___x_367_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_box(v___x_350_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object* v___x_377_, lean_object* v_p_378_, lean_object* v_e_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v___x_214968__boxed_391_; lean_object* v_res_392_; 
v___x_214968__boxed_391_ = lean_unbox(v___x_377_);
v_res_392_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_214968__boxed_391_, v_p_378_, v_e_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(lean_object* v_msgData_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_env_400_; lean_object* v___x_401_; lean_object* v_mctx_402_; lean_object* v_lctx_403_; lean_object* v_options_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_399_ = lean_st_ref_get(v___y_397_);
v_env_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc_ref(v_env_400_);
lean_dec(v___x_399_);
v___x_401_ = lean_st_ref_get(v___y_395_);
v_mctx_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_mctx_402_);
lean_dec(v___x_401_);
v_lctx_403_ = lean_ctor_get(v___y_394_, 2);
v_options_404_ = lean_ctor_get(v___y_396_, 2);
lean_inc_ref(v_options_404_);
lean_inc_ref(v_lctx_403_);
v___x_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_405_, 0, v_env_400_);
lean_ctor_set(v___x_405_, 1, v_mctx_402_);
lean_ctor_set(v___x_405_, 2, v_lctx_403_);
lean_ctor_set(v___x_405_, 3, v_options_404_);
v___x_406_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_msgData_393_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6___boxed(lean_object* v_msgData_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msgData_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_415_; double v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_float_of_nat(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object* v_cls_420_, lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_ref_427_; lean_object* v___x_428_; lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_473_; 
v_ref_427_ = lean_ctor_get(v___y_424_, 5);
v___x_428_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msg_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_473_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_473_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_473_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v_traceState_434_; lean_object* v_env_435_; lean_object* v_nextMacroScope_436_; lean_object* v_ngen_437_; lean_object* v_auxDeclNGen_438_; lean_object* v_cache_439_; lean_object* v_messages_440_; lean_object* v_infoState_441_; lean_object* v_snapshotTasks_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_472_; 
v___x_433_ = lean_st_ref_take(v___y_425_);
v_traceState_434_ = lean_ctor_get(v___x_433_, 4);
v_env_435_ = lean_ctor_get(v___x_433_, 0);
v_nextMacroScope_436_ = lean_ctor_get(v___x_433_, 1);
v_ngen_437_ = lean_ctor_get(v___x_433_, 2);
v_auxDeclNGen_438_ = lean_ctor_get(v___x_433_, 3);
v_cache_439_ = lean_ctor_get(v___x_433_, 5);
v_messages_440_ = lean_ctor_get(v___x_433_, 6);
v_infoState_441_ = lean_ctor_get(v___x_433_, 7);
v_snapshotTasks_442_ = lean_ctor_get(v___x_433_, 8);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_472_ == 0)
{
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_472_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_snapshotTasks_442_);
lean_inc(v_infoState_441_);
lean_inc(v_messages_440_);
lean_inc(v_cache_439_);
lean_inc(v_traceState_434_);
lean_inc(v_auxDeclNGen_438_);
lean_inc(v_ngen_437_);
lean_inc(v_nextMacroScope_436_);
lean_inc(v_env_435_);
lean_dec(v___x_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_472_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
uint64_t v_tid_446_; lean_object* v_traces_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_471_; 
v_tid_446_ = lean_ctor_get_uint64(v_traceState_434_, sizeof(void*)*1);
v_traces_447_ = lean_ctor_get(v_traceState_434_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_traceState_434_);
if (v_isSharedCheck_471_ == 0)
{
v___x_449_ = v_traceState_434_;
v_isShared_450_ = v_isSharedCheck_471_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_traces_447_);
lean_dec(v_traceState_434_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_471_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; double v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_451_ = lean_box(0);
v___x_452_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0);
v___x_453_ = 0;
v___x_454_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
v___x_455_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_455_, 0, v_cls_420_);
lean_ctor_set(v___x_455_, 1, v___x_451_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
lean_ctor_set_float(v___x_455_, sizeof(void*)*3, v___x_452_);
lean_ctor_set_float(v___x_455_, sizeof(void*)*3 + 8, v___x_452_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*3 + 16, v___x_453_);
v___x_456_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2));
v___x_457_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v_a_429_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_inc(v_ref_427_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_ref_427_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_PersistentArray_push___redArg(v_traces_447_, v___x_458_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_459_);
v___x_461_ = v___x_449_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_459_);
lean_ctor_set_uint64(v_reuseFailAlloc_470_, sizeof(void*)*1, v_tid_446_);
v___x_461_ = v_reuseFailAlloc_470_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 4, v___x_461_);
v___x_463_ = v___x_444_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_env_435_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_nextMacroScope_436_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_ngen_437_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_auxDeclNGen_438_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_469_, 5, v_cache_439_);
lean_ctor_set(v_reuseFailAlloc_469_, 6, v_messages_440_);
lean_ctor_set(v_reuseFailAlloc_469_, 7, v_infoState_441_);
lean_ctor_set(v_reuseFailAlloc_469_, 8, v_snapshotTasks_442_);
v___x_463_ = v_reuseFailAlloc_469_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = lean_st_ref_set(v___y_425_, v___x_463_);
v___x_465_ = lean_box(0);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_465_);
v___x_467_ = v___x_431_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object* v_cls_474_, lean_object* v_msg_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_474_, v_msg_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_keys_482_, lean_object* v_i_483_, lean_object* v_k_484_){
_start:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_array_get_size(v_keys_482_);
v___x_486_ = lean_nat_dec_lt(v_i_483_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec(v_i_483_);
return v___x_486_;
}
else
{
lean_object* v_k_x27_487_; uint8_t v___x_488_; 
v_k_x27_487_ = lean_array_fget_borrowed(v_keys_482_, v_i_483_);
v___x_488_ = l_Lean_instBEqMVarId_beq(v_k_484_, v_k_x27_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_add(v_i_483_, v___x_489_);
lean_dec(v_i_483_);
v_i_483_ = v___x_490_;
goto _start;
}
else
{
lean_dec(v_i_483_);
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_keys_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_492_, v_i_493_, v_k_494_);
lean_dec(v_k_494_);
lean_dec_ref(v_keys_492_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(lean_object* v_x_497_, size_t v_x_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
lean_object* v_es_500_; lean_object* v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v_j_505_; lean_object* v___x_506_; 
v_es_500_ = lean_ctor_get(v_x_497_, 0);
v___x_501_ = lean_box(2);
v___x_502_ = ((size_t)5ULL);
v___x_503_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_504_ = lean_usize_land(v_x_498_, v___x_503_);
v_j_505_ = lean_usize_to_nat(v___x_504_);
v___x_506_ = lean_array_get_borrowed(v___x_501_, v_es_500_, v_j_505_);
lean_dec(v_j_505_);
switch(lean_obj_tag(v___x_506_))
{
case 0:
{
lean_object* v_key_507_; uint8_t v___x_508_; 
v_key_507_ = lean_ctor_get(v___x_506_, 0);
v___x_508_ = l_Lean_instBEqMVarId_beq(v_x_499_, v_key_507_);
return v___x_508_;
}
case 1:
{
lean_object* v_node_509_; size_t v___x_510_; 
v_node_509_ = lean_ctor_get(v___x_506_, 0);
v___x_510_ = lean_usize_shift_right(v_x_498_, v___x_502_);
v_x_497_ = v_node_509_;
v_x_498_ = v___x_510_;
goto _start;
}
default: 
{
uint8_t v___x_512_; 
v___x_512_ = 0;
return v___x_512_;
}
}
}
else
{
lean_object* v_ks_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_ks_513_ = lean_ctor_get(v_x_497_, 0);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_ks_513_, v___x_514_, v_x_499_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
size_t v_x_215177__boxed_519_; uint8_t v_res_520_; lean_object* v_r_521_; 
v_x_215177__boxed_519_ = lean_unbox_usize(v_x_517_);
lean_dec(v_x_517_);
v_res_520_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_516_, v_x_215177__boxed_519_, v_x_518_);
lean_dec(v_x_518_);
lean_dec_ref(v_x_516_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint64_t v___x_524_; size_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = l_Lean_instHashableMVarId_hash(v_x_523_);
v___x_525_ = lean_uint64_to_usize(v___x_524_);
v___x_526_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_522_, v___x_525_, v_x_523_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_527_, v_x_528_);
lean_dec(v_x_528_);
lean_dec_ref(v_x_527_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object* v_mvarId_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; lean_object* v_mctx_535_; lean_object* v_eAssignment_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_534_ = lean_st_ref_get(v___y_532_);
v_mctx_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc_ref(v_mctx_535_);
lean_dec(v___x_534_);
v_eAssignment_536_ = lean_ctor_get(v_mctx_535_, 7);
lean_inc_ref(v_eAssignment_536_);
lean_dec_ref(v_mctx_535_);
v___x_537_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_536_, v_mvarId_531_);
lean_dec_ref(v_eAssignment_536_);
v___x_538_ = lean_box(v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object* v_mvarId_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec(v_mvarId_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object* v_as_544_, size_t v_i_545_, size_t v_stop_546_, lean_object* v_b_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_a_560_; uint8_t v___x_564_; 
v___x_564_ = lean_usize_dec_eq(v_i_545_, v_stop_546_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_565_ = lean_array_uget_borrowed(v_as_544_, v_i_545_);
v___x_568_ = l_Lean_Expr_mvarId_x21(v___x_565_);
v___x_569_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_568_, v___y_555_);
lean_dec(v___x_568_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref(v___x_569_);
v___x_571_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
if (v___x_571_ == 0)
{
goto v___jp_566_;
}
else
{
v_a_560_ = v_b_547_;
goto v___jp_559_;
}
}
else
{
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_572_; uint8_t v___x_573_; 
v_a_572_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_569_);
v___x_573_ = lean_unbox(v_a_572_);
lean_dec(v_a_572_);
if (v___x_573_ == 0)
{
v_a_560_ = v_b_547_;
goto v___jp_559_;
}
else
{
goto v___jp_566_;
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_b_547_);
v_a_574_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_569_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_569_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
v___jp_566_:
{
lean_object* v___x_567_; 
lean_inc(v___x_565_);
v___x_567_ = lean_array_push(v_b_547_, v___x_565_);
v_a_560_ = v___x_567_;
goto v___jp_559_;
}
}
else
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_b_547_);
return v___x_582_;
}
v___jp_559_:
{
size_t v___x_561_; size_t v___x_562_; 
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_i_545_, v___x_561_);
v_i_545_ = v___x_562_;
v_b_547_ = v_a_560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object* v_as_583_, lean_object* v_i_584_, lean_object* v_stop_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
size_t v_i_boxed_598_; size_t v_stop_boxed_599_; lean_object* v_res_600_; 
v_i_boxed_598_ = lean_unbox_usize(v_i_584_);
lean_dec(v_i_584_);
v_stop_boxed_599_ = lean_unbox_usize(v_stop_585_);
lean_dec(v_stop_585_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_583_, v_i_boxed_598_, v_stop_boxed_599_, v_b_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v_as_583_);
return v_res_600_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3));
v___x_608_ = l_Lean_stringToMessageData(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object* v___x_609_, lean_object* v_e_610_, lean_object* v_as_611_, size_t v_sz_612_, size_t v_i_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_a_627_; uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_lt(v_i_613_, v_sz_612_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
lean_dec_ref(v_e_610_);
lean_dec(v___x_609_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_b_614_);
return v___x_632_;
}
else
{
lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_739_; 
v_snd_633_ = lean_ctor_get(v_b_614_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_b_614_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v_b_614_, 0);
lean_dec(v_unused_740_);
v___x_635_ = v_b_614_;
v_isShared_636_ = v_isSharedCheck_739_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_dec(v_b_614_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_739_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_array_637_; lean_object* v_start_638_; lean_object* v_stop_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_array_637_ = lean_ctor_get(v_snd_633_, 0);
v_start_638_ = lean_ctor_get(v_snd_633_, 1);
v_stop_639_ = lean_ctor_get(v_snd_633_, 2);
v___x_640_ = lean_box(0);
v___x_641_ = lean_nat_dec_lt(v_start_638_, v_stop_639_);
if (v___x_641_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_e_610_);
lean_dec(v___x_609_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_640_);
v___x_643_ = v___x_635_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_snd_633_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
else
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_735_; 
lean_inc(v_stop_639_);
lean_inc(v_start_638_);
lean_inc_ref(v_array_637_);
v_isSharedCheck_735_ = !lean_is_exclusive(v_snd_633_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; lean_object* v_unused_737_; lean_object* v_unused_738_; 
v_unused_736_ = lean_ctor_get(v_snd_633_, 2);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_snd_633_, 1);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_snd_633_, 0);
lean_dec(v_unused_738_);
v___x_647_ = v_snd_633_;
v_isShared_648_ = v_isSharedCheck_735_;
goto v_resetjp_646_;
}
else
{
lean_dec(v_snd_633_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_735_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v_a_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_a_649_ = lean_array_uget_borrowed(v_as_611_, v_i_613_);
v___x_650_ = l_Lean_Expr_mvarId_x21(v_a_649_);
v___x_651_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_650_, v___y_622_);
lean_dec(v___x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_726_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_726_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_726_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_726_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_656_ = lean_array_fget(v_array_637_, v_start_638_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_start_638_, v___x_657_);
lean_dec(v_start_638_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_658_);
v___x_660_ = v___x_647_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_array_637_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_stop_639_);
v___x_660_ = v_reuseFailAlloc_725_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
uint8_t v___y_672_; uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_unbox(v___x_656_);
lean_dec(v___x_656_);
v___x_723_ = l_Lean_BinderInfo_isInstImplicit(v___x_722_);
if (v___x_723_ == 0)
{
lean_dec(v_a_652_);
v___y_672_ = v___x_723_;
goto v___jp_671_;
}
else
{
uint8_t v___x_724_; 
v___x_724_ = lean_unbox(v_a_652_);
lean_dec(v_a_652_);
if (v___x_724_ == 0)
{
v___y_672_ = v___x_723_;
goto v___jp_671_;
}
else
{
lean_del_object(v___x_654_);
lean_del_object(v___x_635_);
goto v___jp_669_;
}
}
v___jp_661_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0));
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_660_);
lean_ctor_set(v___x_635_, 0, v___x_662_);
v___x_664_ = v___x_635_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_660_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_664_);
v___x_666_ = v___x_654_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
v___jp_669_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_640_);
lean_ctor_set(v___x_670_, 1, v___x_660_);
v_a_627_ = v___x_670_;
goto v___jp_626_;
}
v___jp_671_:
{
if (v___y_672_ == 0)
{
lean_del_object(v___x_654_);
lean_del_object(v___x_635_);
goto v___jp_669_;
}
else
{
lean_object* v___x_673_; 
lean_inc(v___y_624_);
lean_inc_ref(v___y_623_);
lean_inc(v___y_622_);
lean_inc_ref(v___y_621_);
lean_inc(v_a_649_);
v___x_673_ = lean_infer_type(v_a_649_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_673_);
lean_inc(v_a_649_);
v___x_675_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_a_649_, v_a_674_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; uint8_t v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v___x_675_);
v___x_677_ = lean_unbox(v_a_676_);
lean_dec(v_a_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_619_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; uint8_t v___x_680_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref(v___x_678_);
v___x_680_ = lean_unbox(v_a_679_);
lean_dec(v_a_679_);
if (v___x_680_ == 0)
{
lean_dec_ref(v_e_610_);
lean_dec(v___x_609_);
goto v___jp_661_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
v___x_682_ = l_Lean_MessageData_ofName(v___x_609_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_indentExpr(v_e_610_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Lean_Meta_Sym_reportIssue(v___x_687_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_dec_ref(v___x_688_);
goto v___jp_661_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v___x_660_);
lean_del_object(v___x_654_);
lean_del_object(v___x_635_);
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v___x_660_);
lean_del_object(v___x_654_);
lean_del_object(v___x_635_);
lean_dec_ref(v_e_610_);
lean_dec(v___x_609_);
v_a_697_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_678_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_678_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v___x_705_; 
lean_del_object(v___x_654_);
lean_del_object(v___x_635_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_640_);
lean_ctor_set(v___x_705_, 1, v___x_660_);
v_a_627_ = v___x_705_;
goto v___jp_626_;
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v___x_660_);
lean_del_object(v___x_654_);
lean_del_object(v___x_635_);
lean_dec_ref(v_e_610_);
lean_dec(v___x_609_);
v_a_706_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_675_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_675_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v___x_660_);
lean_del_object(v___x_654_);
lean_del_object(v___x_635_);
lean_dec_ref(v_e_610_);
lean_dec(v___x_609_);
v_a_714_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_673_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_673_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
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
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_del_object(v___x_647_);
lean_dec(v_stop_639_);
lean_dec(v_start_638_);
lean_dec_ref(v_array_637_);
lean_del_object(v___x_635_);
lean_dec_ref(v_e_610_);
lean_dec(v___x_609_);
v_a_727_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_651_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_651_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
}
v___jp_626_:
{
size_t v___x_628_; size_t v___x_629_; 
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_613_, v___x_628_);
v_i_613_ = v___x_629_;
v_b_614_ = v_a_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object** _args){
lean_object* v___x_741_ = _args[0];
lean_object* v_e_742_ = _args[1];
lean_object* v_as_743_ = _args[2];
lean_object* v_sz_744_ = _args[3];
lean_object* v_i_745_ = _args[4];
lean_object* v_b_746_ = _args[5];
lean_object* v___y_747_ = _args[6];
lean_object* v___y_748_ = _args[7];
lean_object* v___y_749_ = _args[8];
lean_object* v___y_750_ = _args[9];
lean_object* v___y_751_ = _args[10];
lean_object* v___y_752_ = _args[11];
lean_object* v___y_753_ = _args[12];
lean_object* v___y_754_ = _args[13];
lean_object* v___y_755_ = _args[14];
lean_object* v___y_756_ = _args[15];
lean_object* v___y_757_ = _args[16];
_start:
{
size_t v_sz_boxed_758_; size_t v_i_boxed_759_; lean_object* v_res_760_; 
v_sz_boxed_758_ = lean_unbox_usize(v_sz_744_);
lean_dec(v_sz_744_);
v_i_boxed_759_ = lean_unbox_usize(v_i_745_);
lean_dec(v_i_745_);
v_res_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_741_, v_e_742_, v_as_743_, v_sz_boxed_758_, v_i_boxed_759_, v_b_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v_as_743_);
return v_res_760_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_773_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6));
v___x_774_ = l_Lean_Name_append(v___x_773_, v___x_772_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8));
v___x_777_ = l_Lean_stringToMessageData(v___x_776_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10));
v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12));
v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
return v___x_783_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14));
v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18));
v___x_795_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17));
v___x_796_ = l_Lean_mkConst(v___x_795_, v___x_794_);
return v___x_796_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21(void){
_start:
{
uint8_t v___x_799_; uint64_t v___x_800_; 
v___x_799_ = 1;
v___x_800_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object* v_e_801_, lean_object* v_thm_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_801_, v___y_803_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_826_);
v___x_828_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_805_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_1168_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_1168_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_1168_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_lt(v_a_827_, v_a_829_);
lean_dec(v_a_829_);
lean_dec(v_a_827_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec_ref(v_thm_802_);
lean_dec_ref(v_e_801_);
v___x_834_ = lean_box(0);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_834_);
v___x_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v___x_838_; uint8_t v___x_839_; 
lean_del_object(v___x_831_);
lean_inc_ref(v_e_801_);
v___x_838_ = l_Lean_Expr_cleanupAnnotations(v_e_801_);
v___x_839_ = l_Lean_Expr_isApp(v___x_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v___x_838_);
lean_dec_ref(v_thm_802_);
lean_dec_ref(v_e_801_);
goto v___jp_823_;
}
else
{
lean_object* v_arg_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_arg_840_ = lean_ctor_get(v___x_838_, 1);
lean_inc_ref(v_arg_840_);
v___x_841_ = l_Lean_Expr_appFnCleanup___redArg(v___x_838_);
v___x_842_ = l_Lean_Expr_isApp(v___x_841_);
if (v___x_842_ == 0)
{
lean_dec_ref(v___x_841_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_thm_802_);
lean_dec_ref(v_e_801_);
goto v___jp_823_;
}
else
{
lean_object* v_arg_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_arg_843_ = lean_ctor_get(v___x_841_, 1);
lean_inc_ref(v_arg_843_);
v___x_844_ = l_Lean_Expr_appFnCleanup___redArg(v___x_841_);
v___x_845_ = l_Lean_Expr_isApp(v___x_844_);
if (v___x_845_ == 0)
{
lean_dec_ref(v___x_844_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_thm_802_);
lean_dec_ref(v_e_801_);
goto v___jp_823_;
}
else
{
lean_object* v_arg_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_arg_846_ = lean_ctor_get(v___x_844_, 1);
lean_inc_ref(v_arg_846_);
v___x_847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_844_);
v___x_848_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1));
v___x_849_ = l_Lean_Expr_isConstOf(v___x_847_, v___x_848_);
lean_dec_ref(v___x_847_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_arg_846_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_thm_802_);
lean_dec_ref(v_e_801_);
goto v___jp_823_;
}
else
{
lean_object* v_declName_850_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_879_; lean_object* v___y_880_; uint8_t v___y_881_; lean_object* v___y_916_; uint8_t v___y_917_; lean_object* v_a_918_; lean_object* v___y_946_; uint8_t v___y_947_; lean_object* v___y_948_; lean_object* v___y_959_; lean_object* v___x_983_; 
v_declName_850_ = lean_ctor_get(v_thm_802_, 0);
lean_inc_n(v_declName_850_, 2);
lean_dec_ref(v_thm_802_);
v___x_983_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_850_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; uint8_t v___y_989_; lean_object* v___y_990_; lean_object* v_a_1061_; lean_object* v___x_1092_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc_n(v_a_984_, 2);
lean_dec_ref(v___x_983_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_1092_ = lean_infer_type(v_a_984_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; uint8_t v_foApprox_1095_; uint8_t v_ctxApprox_1096_; uint8_t v_quasiPatternApprox_1097_; uint8_t v_constApprox_1098_; uint8_t v_isDefEqStuckEx_1099_; uint8_t v_unificationHints_1100_; uint8_t v_proofIrrelevance_1101_; uint8_t v_assignSyntheticOpaque_1102_; uint8_t v_offsetCnstrs_1103_; uint8_t v_etaStruct_1104_; uint8_t v_univApprox_1105_; uint8_t v_iota_1106_; uint8_t v_beta_1107_; uint8_t v_proj_1108_; uint8_t v_zeta_1109_; uint8_t v_zetaDelta_1110_; uint8_t v_zetaUnused_1111_; uint8_t v_zetaHave_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1151_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = l_Lean_Meta_Context_config(v___y_809_);
v_foApprox_1095_ = lean_ctor_get_uint8(v___x_1094_, 0);
v_ctxApprox_1096_ = lean_ctor_get_uint8(v___x_1094_, 1);
v_quasiPatternApprox_1097_ = lean_ctor_get_uint8(v___x_1094_, 2);
v_constApprox_1098_ = lean_ctor_get_uint8(v___x_1094_, 3);
v_isDefEqStuckEx_1099_ = lean_ctor_get_uint8(v___x_1094_, 4);
v_unificationHints_1100_ = lean_ctor_get_uint8(v___x_1094_, 5);
v_proofIrrelevance_1101_ = lean_ctor_get_uint8(v___x_1094_, 6);
v_assignSyntheticOpaque_1102_ = lean_ctor_get_uint8(v___x_1094_, 7);
v_offsetCnstrs_1103_ = lean_ctor_get_uint8(v___x_1094_, 8);
v_etaStruct_1104_ = lean_ctor_get_uint8(v___x_1094_, 10);
v_univApprox_1105_ = lean_ctor_get_uint8(v___x_1094_, 11);
v_iota_1106_ = lean_ctor_get_uint8(v___x_1094_, 12);
v_beta_1107_ = lean_ctor_get_uint8(v___x_1094_, 13);
v_proj_1108_ = lean_ctor_get_uint8(v___x_1094_, 14);
v_zeta_1109_ = lean_ctor_get_uint8(v___x_1094_, 15);
v_zetaDelta_1110_ = lean_ctor_get_uint8(v___x_1094_, 16);
v_zetaUnused_1111_ = lean_ctor_get_uint8(v___x_1094_, 17);
v_zetaHave_1112_ = lean_ctor_get_uint8(v___x_1094_, 18);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1114_ = v___x_1094_;
v_isShared_1115_ = v_isSharedCheck_1151_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v___x_1094_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1151_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
uint8_t v_trackZetaDelta_1116_; lean_object* v_zetaDeltaSet_1117_; lean_object* v_lctx_1118_; lean_object* v_localInstances_1119_; lean_object* v_defEqCtx_x3f_1120_; lean_object* v_synthPendingDepth_1121_; lean_object* v_canUnfold_x3f_1122_; uint8_t v_univApprox_1123_; uint8_t v_inTypeClassResolution_1124_; uint8_t v_cacheInferType_1125_; uint8_t v___x_1126_; lean_object* v_config_1128_; 
v_trackZetaDelta_1116_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*7);
v_zetaDeltaSet_1117_ = lean_ctor_get(v___y_809_, 1);
v_lctx_1118_ = lean_ctor_get(v___y_809_, 2);
v_localInstances_1119_ = lean_ctor_get(v___y_809_, 3);
v_defEqCtx_x3f_1120_ = lean_ctor_get(v___y_809_, 4);
v_synthPendingDepth_1121_ = lean_ctor_get(v___y_809_, 5);
v_canUnfold_x3f_1122_ = lean_ctor_get(v___y_809_, 6);
v_univApprox_1123_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1124_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*7 + 2);
v_cacheInferType_1125_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*7 + 3);
v___x_1126_ = 1;
if (v_isShared_1115_ == 0)
{
v_config_1128_ = v___x_1114_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 0, v_foApprox_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 1, v_ctxApprox_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 2, v_quasiPatternApprox_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 3, v_constApprox_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 4, v_isDefEqStuckEx_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 5, v_unificationHints_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 6, v_proofIrrelevance_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 7, v_assignSyntheticOpaque_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 8, v_offsetCnstrs_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 10, v_etaStruct_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 11, v_univApprox_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 12, v_iota_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 13, v_beta_1107_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 14, v_proj_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 15, v_zeta_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 16, v_zetaDelta_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 17, v_zetaUnused_1111_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, 18, v_zetaHave_1112_);
v_config_1128_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
uint64_t v___x_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; uint64_t v___x_1134_; uint64_t v___x_1135_; uint64_t v_key_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_ctor_set_uint8(v_config_1128_, 9, v___x_1126_);
v___x_1129_ = l_Lean_Meta_Context_configKey(v___y_809_);
v___x_1130_ = 2ULL;
v___x_1131_ = lean_uint64_shift_right(v___x_1129_, v___x_1130_);
v___x_1132_ = lean_box(0);
v___x_1133_ = 0;
v___x_1134_ = lean_uint64_shift_left(v___x_1131_, v___x_1130_);
v___x_1135_ = lean_uint64_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21);
v_key_1136_ = lean_uint64_lor(v___x_1134_, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1137_, 0, v_config_1128_);
lean_ctor_set_uint64(v___x_1137_, sizeof(void*)*1, v_key_1136_);
lean_inc(v_canUnfold_x3f_1122_);
lean_inc(v_synthPendingDepth_1121_);
lean_inc(v_defEqCtx_x3f_1120_);
lean_inc_ref(v_localInstances_1119_);
lean_inc_ref(v_lctx_1118_);
lean_inc(v_zetaDeltaSet_1117_);
v___x_1138_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v_zetaDeltaSet_1117_);
lean_ctor_set(v___x_1138_, 2, v_lctx_1118_);
lean_ctor_set(v___x_1138_, 3, v_localInstances_1119_);
lean_ctor_set(v___x_1138_, 4, v_defEqCtx_x3f_1120_);
lean_ctor_set(v___x_1138_, 5, v_synthPendingDepth_1121_);
lean_ctor_set(v___x_1138_, 6, v_canUnfold_x3f_1122_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*7, v_trackZetaDelta_1116_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*7 + 1, v_univApprox_1123_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1124_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*7 + 3, v_cacheInferType_1125_);
v___x_1139_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1093_, v___x_1132_, v___x_1133_, v___x_1138_, v___y_810_, v___y_811_, v___y_812_);
lean_dec_ref(v___x_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref(v___x_1139_);
v_a_1061_ = v_a_1140_;
goto v___jp_1060_;
}
else
{
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1141_; 
v_a_1141_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v___x_1139_);
v_a_1061_ = v_a_1141_;
goto v___jp_1060_;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_arg_846_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_e_801_);
v_a_1142_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1139_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
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
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_arg_846_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_e_801_);
v_a_1152_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1092_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1092_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
v___jp_985_:
{
if (lean_obj_tag(v___y_990_) == 0)
{
lean_object* v_a_991_; uint8_t v___x_992_; 
v_a_991_ = lean_ctor_get(v___y_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref(v___y_990_);
v___x_992_ = lean_unbox(v_a_991_);
lean_dec(v_a_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_a_984_);
v___y_959_ = v___y_988_;
goto v___jp_958_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; size_t v_sz_998_; size_t v___x_999_; lean_object* v___x_1000_; 
lean_dec_ref(v___y_988_);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v___y_987_);
v___x_995_ = l_Array_toSubarray___redArg(v___y_987_, v___x_993_, v___x_994_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_995_);
v_sz_998_ = lean_array_size(v___y_986_);
v___x_999_ = ((size_t)0ULL);
lean_inc_ref(v_e_801_);
lean_inc(v_declName_850_);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_850_, v_e_801_, v___y_986_, v_sz_998_, v___x_999_, v___x_997_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1043_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1043_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1043_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_fst_1005_; 
v_fst_1005_ = lean_ctor_get(v_a_1001_, 0);
lean_inc(v_fst_1005_);
lean_dec(v_a_1001_);
if (lean_obj_tag(v_fst_1005_) == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_a_1008_; lean_object* v___x_1009_; 
lean_del_object(v___x_1003_);
v___x_1006_ = l_Lean_mkAppN(v_a_984_, v___y_986_);
v___x_1007_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_1006_, v___y_810_);
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref(v___x_1007_);
lean_inc_ref(v_e_801_);
v___x_1009_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_801_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_807_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19);
lean_inc_ref(v_e_801_);
v___x_1014_ = l_Lean_mkApp4(v___x_1013_, v_e_801_, v_a_1012_, v_a_1010_, v_a_1008_);
v___x_1015_ = lean_array_get_size(v___y_986_);
v___x_1016_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20));
v___x_1017_ = lean_nat_dec_lt(v___x_993_, v___x_1015_);
if (v___x_1017_ == 0)
{
lean_dec_ref(v___y_986_);
v___y_916_ = v___x_1014_;
v___y_917_ = v___y_989_;
v_a_918_ = v___x_1016_;
goto v___jp_915_;
}
else
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_nat_dec_le(v___x_1015_, v___x_1015_);
if (v___x_1018_ == 0)
{
if (v___x_1017_ == 0)
{
lean_dec_ref(v___y_986_);
v___y_916_ = v___x_1014_;
v___y_917_ = v___y_989_;
v_a_918_ = v___x_1016_;
goto v___jp_915_;
}
else
{
size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_usize_of_nat(v___x_1015_);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_986_, v___x_999_, v___x_1019_, v___x_1016_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec_ref(v___y_986_);
v___y_946_ = v___x_1014_;
v___y_947_ = v___y_989_;
v___y_948_ = v___x_1020_;
goto v___jp_945_;
}
}
else
{
size_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_usize_of_nat(v___x_1015_);
v___x_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_986_, v___x_999_, v___x_1021_, v___x_1016_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec_ref(v___y_986_);
v___y_946_ = v___x_1014_;
v___y_947_ = v___y_989_;
v___y_948_ = v___x_1022_;
goto v___jp_945_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_1010_);
lean_dec(v_a_1008_);
lean_dec_ref(v___y_986_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_1023_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1011_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1011_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_a_1008_);
lean_dec_ref(v___y_986_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_1031_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1009_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1009_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1041_; 
lean_dec_ref(v___y_986_);
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_val_1039_ = lean_ctor_get(v_fst_1005_, 0);
lean_inc(v_val_1039_);
lean_dec_ref(v_fst_1005_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v_val_1039_);
v___x_1041_ = v___x_1003_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_val_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v___y_986_);
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_1044_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1000_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1000_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_1052_ = lean_ctor_get(v___y_990_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___y_990_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___y_990_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___y_990_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
v___jp_1060_:
{
lean_object* v_snd_1062_; lean_object* v_fst_1063_; lean_object* v_fst_1064_; lean_object* v_snd_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_snd_1062_ = lean_ctor_get(v_a_1061_, 1);
lean_inc(v_snd_1062_);
v_fst_1063_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_fst_1063_);
lean_dec_ref(v_a_1061_);
v_fst_1064_ = lean_ctor_get(v_snd_1062_, 0);
lean_inc(v_fst_1064_);
v_snd_1065_ = lean_ctor_get(v_snd_1062_, 1);
lean_inc_n(v_snd_1065_, 2);
lean_dec(v_snd_1062_);
v___x_1066_ = l_Lean_Expr_cleanupAnnotations(v_snd_1065_);
v___x_1067_ = l_Lean_Expr_isApp(v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v___x_1066_);
lean_dec(v_snd_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_arg_846_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_e_801_);
goto v___jp_820_;
}
else
{
lean_object* v_arg_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_arg_1068_ = lean_ctor_get(v___x_1066_, 1);
lean_inc_ref(v_arg_1068_);
v___x_1069_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1066_);
v___x_1070_ = l_Lean_Expr_isApp(v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec_ref(v___x_1069_);
lean_dec_ref(v_arg_1068_);
lean_dec(v_snd_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_arg_846_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_e_801_);
goto v___jp_820_;
}
else
{
lean_object* v_arg_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_arg_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc_ref(v_arg_1071_);
v___x_1072_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1069_);
v___x_1073_ = l_Lean_Expr_isApp(v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec(v_snd_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_arg_846_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_e_801_);
goto v___jp_820_;
}
else
{
lean_object* v_arg_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_arg_1074_ = lean_ctor_get(v___x_1072_, 1);
lean_inc_ref(v_arg_1074_);
v___x_1075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1072_);
v___x_1076_ = l_Lean_Expr_isConstOf(v___x_1075_, v___x_848_);
lean_dec_ref(v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec(v_snd_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_arg_846_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_e_801_);
goto v___jp_820_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Meta_isExprDefEq(v_arg_846_, v_arg_1074_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; uint8_t v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
v___x_1079_ = lean_unbox(v_a_1078_);
lean_dec(v_a_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
v___y_986_ = v_fst_1063_;
v___y_987_ = v_fst_1064_;
v___y_988_ = v_snd_1065_;
v___y_989_ = v___x_1076_;
v___y_990_ = v___x_1077_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1080_; 
lean_dec_ref(v___x_1077_);
v___x_1080_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1076_, v_arg_1071_, v_arg_843_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; uint8_t v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v___x_1080_);
v___x_1082_ = lean_unbox(v_a_1081_);
lean_dec(v_a_1081_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v_arg_1068_);
lean_dec(v_fst_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_a_984_);
lean_dec_ref(v_arg_840_);
v___y_959_ = v_snd_1065_;
goto v___jp_958_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1076_, v_arg_1068_, v_arg_840_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
v___y_986_ = v_fst_1063_;
v___y_987_ = v_fst_1064_;
v___y_988_ = v_snd_1065_;
v___y_989_ = v___x_1076_;
v___y_990_ = v___x_1083_;
goto v___jp_985_;
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v_arg_1068_);
lean_dec(v_snd_1065_);
lean_dec(v_fst_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_a_984_);
lean_dec(v_declName_850_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_e_801_);
v_a_1084_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1080_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1080_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
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
}
else
{
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
v___y_986_ = v_fst_1063_;
v___y_987_ = v_fst_1064_;
v___y_988_ = v_snd_1065_;
v___y_989_ = v___x_1076_;
v___y_990_ = v___x_1077_;
goto v___jp_985_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v_declName_850_);
lean_dec_ref(v_arg_846_);
lean_dec_ref(v_arg_843_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_e_801_);
v_a_1160_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_983_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_983_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
v___jp_851_:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_801_, v___y_854_);
lean_dec_ref(v_e_801_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_add(v_a_865_, v___x_866_);
lean_dec(v_a_865_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v_declName_850_);
v___x_869_ = l_Lean_Meta_Grind_addNewRawFact(v___y_852_, v___y_853_, v___x_867_, v___x_868_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_869_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v_declName_850_);
v_a_870_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_864_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_864_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
v___jp_878_:
{
if (v___y_881_ == 0)
{
lean_object* v_options_882_; uint8_t v_hasTrace_883_; 
v_options_882_ = lean_ctor_get(v___y_811_, 2);
v_hasTrace_883_ = lean_ctor_get_uint8(v_options_882_, sizeof(void*)*1);
if (v_hasTrace_883_ == 0)
{
v___y_852_ = v___y_879_;
v___y_853_ = v___y_880_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
goto v___jp_851_;
}
else
{
lean_object* v_inheritedTraceOptions_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_inheritedTraceOptions_884_ = lean_ctor_get(v___y_811_, 13);
v___x_885_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_886_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7);
v___x_887_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_884_, v_options_882_, v___x_886_);
if (v___x_887_ == 0)
{
v___y_852_ = v___y_879_;
v___y_853_ = v___y_880_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
goto v___jp_851_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_inc(v_declName_850_);
v___x_888_ = l_Lean_MessageData_ofName(v_declName_850_);
v___x_889_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
lean_inc_ref(v___y_880_);
v___x_891_ = l_Lean_MessageData_ofExpr(v___y_880_);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_885_, v___x_892_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_dec_ref(v___x_893_);
v___y_852_ = v___y_879_;
v___y_853_ = v___y_880_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
goto v___jp_851_;
}
else
{
lean_dec_ref(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
return v___x_893_;
}
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec_ref(v___y_880_);
lean_dec_ref(v___y_879_);
v___x_894_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_807_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; uint8_t v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
v___x_896_ = lean_unbox(v_a_895_);
lean_dec(v_a_895_);
if (v___x_896_ == 0)
{
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
goto v___jp_814_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_897_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_898_ = l_Lean_MessageData_ofName(v_declName_850_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_indentExpr(v_e_801_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_Meta_Sym_reportIssue(v___x_905_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_dec_ref(v___x_906_);
goto v___jp_814_;
}
else
{
return v___x_906_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_907_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_894_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_894_);
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
v___jp_915_:
{
uint8_t v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; 
v___x_919_ = 0;
v___x_920_ = 1;
v___x_921_ = l_Lean_Meta_mkLambdaFVars(v_a_918_, v___y_916_, v___x_919_, v___y_917_, v___x_919_, v___y_917_, v___x_920_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec_ref(v_a_918_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_925_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v___x_923_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_922_, v___y_810_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc_n(v_a_924_, 2);
lean_dec_ref(v___x_923_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_925_ = lean_infer_type(v_a_924_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; uint8_t v___x_927_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v___x_925_);
v___x_927_ = l_Lean_Expr_hasMVar(v_a_924_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
v___x_928_ = l_Lean_Expr_hasMVar(v_a_926_);
v___y_879_ = v_a_924_;
v___y_880_ = v_a_926_;
v___y_881_ = v___x_928_;
goto v___jp_878_;
}
else
{
v___y_879_ = v_a_924_;
v___y_880_ = v_a_926_;
v___y_881_ = v___y_917_;
goto v___jp_878_;
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_924_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_929_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_925_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_925_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_937_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_921_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_921_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
v___jp_945_:
{
if (lean_obj_tag(v___y_948_) == 0)
{
lean_object* v_a_949_; 
v_a_949_ = lean_ctor_get(v___y_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v___y_948_);
v___y_916_ = v___y_946_;
v___y_917_ = v___y_947_;
v_a_918_ = v_a_949_;
goto v___jp_915_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___y_946_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_950_ = lean_ctor_get(v___y_948_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___y_948_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___y_948_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___y_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
v___jp_958_:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_807_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; uint8_t v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v___x_962_ = lean_unbox(v_a_961_);
lean_dec(v_a_961_);
if (v___x_962_ == 0)
{
lean_dec_ref(v___y_959_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
goto v___jp_817_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_963_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_964_ = l_Lean_MessageData_ofName(v_declName_850_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_indentExpr(v_e_801_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_indentExpr(v___y_959_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_Meta_Sym_reportIssue(v___x_973_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_dec_ref(v___x_974_);
goto v___jp_817_;
}
else
{
return v___x_974_;
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v___y_959_);
lean_dec(v_declName_850_);
lean_dec_ref(v_e_801_);
v_a_975_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_960_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_960_);
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_a_827_);
lean_dec_ref(v_thm_802_);
lean_dec_ref(v_e_801_);
v_a_1169_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_828_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_828_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v_thm_802_);
lean_dec_ref(v_e_801_);
v_a_1177_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_826_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_826_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
v___jp_814_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_box(0);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
v___jp_817_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
v___jp_820_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
v___jp_823_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_box(0);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object* v_e_1185_, lean_object* v_thm_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(v_e_1185_, v_thm_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object* v_thm_1199_, lean_object* v_e_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___f_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; 
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed), 13, 2);
lean_closure_set(v___f_1212_, 0, v_e_1200_);
lean_closure_set(v___f_1212_, 1, v_thm_1199_);
v___x_1213_ = 0;
v___x_1214_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v___f_1212_, v___x_1213_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object* v_thm_1215_, lean_object* v_e_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_thm_1215_, v_e_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec(v_a_1217_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object* v_mvarId_1229_, lean_object* v_val_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_1229_, v_val_1230_, v___y_1238_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object* v_mvarId_1243_, lean_object* v_val_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(v_mvarId_1243_, v_val_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object* v_mvarId_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_1257_, v___y_1265_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object* v_mvarId_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(v_mvarId_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec(v_mvarId_1270_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object* v_cls_1283_, lean_object* v_msg_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_1283_, v_msg_1284_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object* v_cls_1297_, lean_object* v_msg_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(v_cls_1297_, v_msg_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec(v___y_1299_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_1312_, v_x_1313_, v_x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object* v_00_u03b2_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1317_, v_x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
uint8_t v_res_1323_; lean_object* v_r_1324_; 
v_res_1323_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(v_00_u03b2_1320_, v_x_1321_, v_x_1322_);
lean_dec(v_x_1322_);
lean_dec_ref(v_x_1321_);
v_r_1324_ = lean_box(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1325_, lean_object* v_x_1326_, size_t v_x_1327_, size_t v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1326_, v_x_1327_, v_x_1328_, v_x_1329_, v_x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_){
_start:
{
size_t v_x_216585__boxed_1338_; size_t v_x_216586__boxed_1339_; lean_object* v_res_1340_; 
v_x_216585__boxed_1338_ = lean_unbox_usize(v_x_1334_);
lean_dec(v_x_1334_);
v_x_216586__boxed_1339_ = lean_unbox_usize(v_x_1335_);
lean_dec(v_x_1335_);
v_res_1340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(v_00_u03b2_1332_, v_x_1333_, v_x_216585__boxed_1338_, v_x_216586__boxed_1339_, v_x_1336_, v_x_1337_);
return v_res_1340_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1341_, lean_object* v_x_1342_, size_t v_x_1343_, lean_object* v_x_1344_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1342_, v_x_1343_, v_x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
size_t v_x_216602__boxed_1350_; uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_x_216602__boxed_1350_ = lean_unbox_usize(v_x_1348_);
lean_dec(v_x_1348_);
v_res_1351_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(v_00_u03b2_1346_, v_x_1347_, v_x_216602__boxed_1350_, v_x_1349_);
lean_dec(v_x_1349_);
lean_dec_ref(v_x_1347_);
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03b2_1353_, lean_object* v_n_1354_, lean_object* v_k_1355_, lean_object* v_v_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_n_1354_, v_k_1355_, v_v_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_1358_, size_t v_depth_1359_, lean_object* v_keys_1360_, lean_object* v_vals_1361_, lean_object* v_heq_1362_, lean_object* v_i_1363_, lean_object* v_entries_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_1359_, v_keys_1360_, v_vals_1361_, v_i_1363_, v_entries_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1366_, lean_object* v_depth_1367_, lean_object* v_keys_1368_, lean_object* v_vals_1369_, lean_object* v_heq_1370_, lean_object* v_i_1371_, lean_object* v_entries_1372_){
_start:
{
size_t v_depth_boxed_1373_; lean_object* v_res_1374_; 
v_depth_boxed_1373_ = lean_unbox_usize(v_depth_1367_);
lean_dec(v_depth_1367_);
v_res_1374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_1366_, v_depth_boxed_1373_, v_keys_1368_, v_vals_1369_, v_heq_1370_, v_i_1371_, v_entries_1372_);
lean_dec_ref(v_vals_1369_);
lean_dec_ref(v_keys_1368_);
return v_res_1374_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_1375_, lean_object* v_keys_1376_, lean_object* v_vals_1377_, lean_object* v_heq_1378_, lean_object* v_i_1379_, lean_object* v_k_1380_){
_start:
{
uint8_t v___x_1381_; 
v___x_1381_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_1376_, v_i_1379_, v_k_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(lean_object* v_00_u03b2_1382_, lean_object* v_keys_1383_, lean_object* v_vals_1384_, lean_object* v_heq_1385_, lean_object* v_i_1386_, lean_object* v_k_1387_){
_start:
{
uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_res_1388_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(v_00_u03b2_1382_, v_keys_1383_, v_vals_1384_, v_heq_1385_, v_i_1386_, v_k_1387_);
lean_dec(v_k_1387_);
lean_dec_ref(v_vals_1384_);
lean_dec_ref(v_keys_1383_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11(lean_object* v_00_u03b2_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_x_1391_, v_x_1392_, v_x_1393_, v_x_1394_);
return v___x_1395_;
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
