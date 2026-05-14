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
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_215300__boxed_298_; size_t v_x_215301__boxed_299_; lean_object* v_res_300_; 
v_x_215300__boxed_298_ = lean_unbox_usize(v_x_294_);
lean_dec(v_x_294_);
v_x_215301__boxed_299_ = lean_unbox_usize(v_x_295_);
lean_dec(v_x_295_);
v_res_300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_293_, v_x_215300__boxed_298_, v_x_215301__boxed_299_, v_x_296_, v_x_297_);
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
uint8_t v___x_215519__boxed_392_; lean_object* v_res_393_; 
v___x_215519__boxed_392_ = lean_unbox(v___x_378_);
v_res_393_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_215519__boxed_392_, v_p_379_, v_e_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
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
lean_object* v_ref_428_; lean_object* v___x_429_; lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_475_; 
v_ref_428_ = lean_ctor_get(v___y_425_, 5);
v___x_429_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_475_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_475_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_475_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v_traceState_435_; lean_object* v_env_436_; lean_object* v_nextMacroScope_437_; lean_object* v_ngen_438_; lean_object* v_auxDeclNGen_439_; lean_object* v_cache_440_; lean_object* v_messages_441_; lean_object* v_infoState_442_; lean_object* v_snapshotTasks_443_; lean_object* v_newDecls_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_474_; 
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
v_newDecls_444_ = lean_ctor_get(v___x_434_, 9);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_474_ == 0)
{
v___x_446_ = v___x_434_;
v_isShared_447_ = v_isSharedCheck_474_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_newDecls_444_);
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
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_474_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint64_t v_tid_448_; lean_object* v_traces_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_473_; 
v_tid_448_ = lean_ctor_get_uint64(v_traceState_435_, sizeof(void*)*1);
v_traces_449_ = lean_ctor_get(v_traceState_435_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_traceState_435_);
if (v_isSharedCheck_473_ == 0)
{
v___x_451_ = v_traceState_435_;
v_isShared_452_ = v_isSharedCheck_473_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_traces_449_);
lean_dec(v_traceState_435_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_473_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; double v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0);
v___x_455_ = 0;
v___x_456_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
v___x_457_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_457_, 0, v_cls_421_);
lean_ctor_set(v___x_457_, 1, v___x_453_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_ctor_set_float(v___x_457_, sizeof(void*)*3, v___x_454_);
lean_ctor_set_float(v___x_457_, sizeof(void*)*3 + 8, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 16, v___x_455_);
v___x_458_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2));
v___x_459_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v_a_430_);
lean_ctor_set(v___x_459_, 2, v___x_458_);
lean_inc(v_ref_428_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_ref_428_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_PersistentArray_push___redArg(v_traces_449_, v___x_460_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_461_);
v___x_463_ = v___x_451_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_461_);
lean_ctor_set_uint64(v_reuseFailAlloc_472_, sizeof(void*)*1, v_tid_448_);
v___x_463_ = v_reuseFailAlloc_472_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 4, v___x_463_);
v___x_465_ = v___x_446_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_env_436_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_nextMacroScope_437_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_ngen_438_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_auxDeclNGen_439_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_471_, 5, v_cache_440_);
lean_ctor_set(v_reuseFailAlloc_471_, 6, v_messages_441_);
lean_ctor_set(v_reuseFailAlloc_471_, 7, v_infoState_442_);
lean_ctor_set(v_reuseFailAlloc_471_, 8, v_snapshotTasks_443_);
lean_ctor_set(v_reuseFailAlloc_471_, 9, v_newDecls_444_);
v___x_465_ = v_reuseFailAlloc_471_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = lean_st_ref_set(v___y_426_, v___x_465_);
v___x_467_ = lean_box(0);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_467_);
v___x_469_ = v___x_432_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object* v_cls_476_, lean_object* v_msg_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_476_, v_msg_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_483_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_keys_484_, lean_object* v_i_485_, lean_object* v_k_486_){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_array_get_size(v_keys_484_);
v___x_488_ = lean_nat_dec_lt(v_i_485_, v___x_487_);
if (v___x_488_ == 0)
{
lean_dec(v_i_485_);
return v___x_488_;
}
else
{
lean_object* v_k_x27_489_; uint8_t v___x_490_; 
v_k_x27_489_ = lean_array_fget_borrowed(v_keys_484_, v_i_485_);
v___x_490_ = l_Lean_instBEqMVarId_beq(v_k_486_, v_k_x27_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v_i_485_, v___x_491_);
lean_dec(v_i_485_);
v_i_485_ = v___x_492_;
goto _start;
}
else
{
lean_dec(v_i_485_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_keys_494_, lean_object* v_i_495_, lean_object* v_k_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_494_, v_i_495_, v_k_496_);
lean_dec(v_k_496_);
lean_dec_ref(v_keys_494_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(lean_object* v_x_499_, size_t v_x_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_object* v_es_502_; lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; lean_object* v_j_507_; lean_object* v___x_508_; 
v_es_502_ = lean_ctor_get(v_x_499_, 0);
v___x_503_ = lean_box(2);
v___x_504_ = ((size_t)5ULL);
v___x_505_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_506_ = lean_usize_land(v_x_500_, v___x_505_);
v_j_507_ = lean_usize_to_nat(v___x_506_);
v___x_508_ = lean_array_get_borrowed(v___x_503_, v_es_502_, v_j_507_);
lean_dec(v_j_507_);
switch(lean_obj_tag(v___x_508_))
{
case 0:
{
lean_object* v_key_509_; uint8_t v___x_510_; 
v_key_509_ = lean_ctor_get(v___x_508_, 0);
v___x_510_ = l_Lean_instBEqMVarId_beq(v_x_501_, v_key_509_);
return v___x_510_;
}
case 1:
{
lean_object* v_node_511_; size_t v___x_512_; 
v_node_511_ = lean_ctor_get(v___x_508_, 0);
v___x_512_ = lean_usize_shift_right(v_x_500_, v___x_504_);
v_x_499_ = v_node_511_;
v_x_500_ = v___x_512_;
goto _start;
}
default: 
{
uint8_t v___x_514_; 
v___x_514_ = 0;
return v___x_514_;
}
}
}
else
{
lean_object* v_ks_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_ks_515_ = lean_ctor_get(v_x_499_, 0);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_ks_515_, v___x_516_, v_x_501_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
size_t v_x_215728__boxed_521_; uint8_t v_res_522_; lean_object* v_r_523_; 
v_x_215728__boxed_521_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_res_522_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_518_, v_x_215728__boxed_521_, v_x_520_);
lean_dec(v_x_520_);
lean_dec_ref(v_x_518_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
uint64_t v___x_526_; size_t v___x_527_; uint8_t v___x_528_; 
v___x_526_ = l_Lean_instHashableMVarId_hash(v_x_525_);
v___x_527_ = lean_uint64_to_usize(v___x_526_);
v___x_528_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_524_, v___x_527_, v_x_525_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_529_, v_x_530_);
lean_dec(v_x_530_);
lean_dec_ref(v_x_529_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object* v_mvarId_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; lean_object* v_mctx_537_; lean_object* v_eAssignment_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_536_ = lean_st_ref_get(v___y_534_);
v_mctx_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc_ref(v_mctx_537_);
lean_dec(v___x_536_);
v_eAssignment_538_ = lean_ctor_get(v_mctx_537_, 8);
lean_inc_ref(v_eAssignment_538_);
lean_dec_ref(v_mctx_537_);
v___x_539_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_538_, v_mvarId_533_);
lean_dec_ref(v_eAssignment_538_);
v___x_540_ = lean_box(v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object* v_mvarId_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec(v_mvarId_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object* v_as_546_, size_t v_i_547_, size_t v_stop_548_, lean_object* v_b_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_a_562_; uint8_t v___x_566_; 
v___x_566_ = lean_usize_dec_eq(v_i_547_, v_stop_548_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_567_ = lean_array_uget_borrowed(v_as_546_, v_i_547_);
v___x_570_ = l_Lean_Expr_mvarId_x21(v___x_567_);
v___x_571_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_570_, v___y_557_);
lean_dec(v___x_570_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; uint8_t v___x_573_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_571_);
v___x_573_ = lean_unbox(v_a_572_);
lean_dec(v_a_572_);
if (v___x_573_ == 0)
{
goto v___jp_568_;
}
else
{
v_a_562_ = v_b_549_;
goto v___jp_561_;
}
}
else
{
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_574_; uint8_t v___x_575_; 
v_a_574_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v___x_571_);
v___x_575_ = lean_unbox(v_a_574_);
lean_dec(v_a_574_);
if (v___x_575_ == 0)
{
v_a_562_ = v_b_549_;
goto v___jp_561_;
}
else
{
goto v___jp_568_;
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_b_549_);
v_a_576_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_571_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_571_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
v___jp_568_:
{
lean_object* v___x_569_; 
lean_inc(v___x_567_);
v___x_569_ = lean_array_push(v_b_549_, v___x_567_);
v_a_562_ = v___x_569_;
goto v___jp_561_;
}
}
else
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_b_549_);
return v___x_584_;
}
v___jp_561_:
{
size_t v___x_563_; size_t v___x_564_; 
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_547_, v___x_563_);
v_i_547_ = v___x_564_;
v_b_549_ = v_a_562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object* v_as_585_, lean_object* v_i_586_, lean_object* v_stop_587_, lean_object* v_b_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
size_t v_i_boxed_600_; size_t v_stop_boxed_601_; lean_object* v_res_602_; 
v_i_boxed_600_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_stop_boxed_601_ = lean_unbox_usize(v_stop_587_);
lean_dec(v_stop_587_);
v_res_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_585_, v_i_boxed_600_, v_stop_boxed_601_, v_b_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v_as_585_);
return v_res_602_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1));
v___x_607_ = l_Lean_stringToMessageData(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3));
v___x_610_ = l_Lean_stringToMessageData(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object* v___x_611_, lean_object* v_e_612_, lean_object* v_as_613_, size_t v_sz_614_, size_t v_i_615_, lean_object* v_b_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_a_629_; uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_lt(v_i_615_, v_sz_614_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec_ref(v_e_612_);
lean_dec(v___x_611_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_b_616_);
return v___x_634_;
}
else
{
lean_object* v_snd_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_741_; 
v_snd_635_ = lean_ctor_get(v_b_616_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_b_616_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_b_616_, 0);
lean_dec(v_unused_742_);
v___x_637_ = v_b_616_;
v_isShared_638_ = v_isSharedCheck_741_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_snd_635_);
lean_dec(v_b_616_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_741_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_array_639_; lean_object* v_start_640_; lean_object* v_stop_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_array_639_ = lean_ctor_get(v_snd_635_, 0);
v_start_640_ = lean_ctor_get(v_snd_635_, 1);
v_stop_641_ = lean_ctor_get(v_snd_635_, 2);
v___x_642_ = lean_box(0);
v___x_643_ = lean_nat_dec_lt(v_start_640_, v_stop_641_);
if (v___x_643_ == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v_e_612_);
lean_dec(v___x_611_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_642_);
v___x_645_ = v___x_637_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_snd_635_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
else
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_737_; 
lean_inc(v_stop_641_);
lean_inc(v_start_640_);
lean_inc_ref(v_array_639_);
v_isSharedCheck_737_ = !lean_is_exclusive(v_snd_635_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; lean_object* v_unused_739_; lean_object* v_unused_740_; 
v_unused_738_ = lean_ctor_get(v_snd_635_, 2);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_snd_635_, 1);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_snd_635_, 0);
lean_dec(v_unused_740_);
v___x_649_ = v_snd_635_;
v_isShared_650_ = v_isSharedCheck_737_;
goto v_resetjp_648_;
}
else
{
lean_dec(v_snd_635_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_737_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_a_651_ = lean_array_uget_borrowed(v_as_613_, v_i_615_);
v___x_652_ = l_Lean_Expr_mvarId_x21(v_a_651_);
v___x_653_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_652_, v___y_624_);
lean_dec(v___x_652_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_728_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_728_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_728_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_728_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_658_ = lean_array_fget(v_array_639_, v_start_640_);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_add(v_start_640_, v___x_659_);
lean_dec(v_start_640_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_660_);
v___x_662_ = v___x_649_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_array_639_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_stop_641_);
v___x_662_ = v_reuseFailAlloc_727_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
uint8_t v___y_674_; uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unbox(v___x_658_);
lean_dec(v___x_658_);
v___x_725_ = l_Lean_BinderInfo_isInstImplicit(v___x_724_);
if (v___x_725_ == 0)
{
lean_dec(v_a_654_);
v___y_674_ = v___x_725_;
goto v___jp_673_;
}
else
{
uint8_t v___x_726_; 
v___x_726_ = lean_unbox(v_a_654_);
lean_dec(v_a_654_);
if (v___x_726_ == 0)
{
v___y_674_ = v___x_725_;
goto v___jp_673_;
}
else
{
lean_del_object(v___x_656_);
lean_del_object(v___x_637_);
goto v___jp_671_;
}
}
v___jp_663_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0));
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_662_);
lean_ctor_set(v___x_637_, 0, v___x_664_);
v___x_666_ = v___x_637_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_662_);
v___x_666_ = v_reuseFailAlloc_670_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_668_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_666_);
v___x_668_ = v___x_656_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
v___jp_671_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_642_);
lean_ctor_set(v___x_672_, 1, v___x_662_);
v_a_629_ = v___x_672_;
goto v___jp_628_;
}
v___jp_673_:
{
if (v___y_674_ == 0)
{
lean_del_object(v___x_656_);
lean_del_object(v___x_637_);
goto v___jp_671_;
}
else
{
lean_object* v___x_675_; 
lean_inc(v___y_626_);
lean_inc_ref(v___y_625_);
lean_inc(v___y_624_);
lean_inc_ref(v___y_623_);
lean_inc(v_a_651_);
v___x_675_ = lean_infer_type(v_a_651_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v___x_675_);
lean_inc(v_a_651_);
v___x_677_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_a_651_, v_a_676_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; uint8_t v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref(v___x_677_);
v___x_679_ = lean_unbox(v_a_678_);
lean_dec(v_a_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_621_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; uint8_t v___x_682_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v___x_680_);
v___x_682_ = lean_unbox(v_a_681_);
lean_dec(v_a_681_);
if (v___x_682_ == 0)
{
lean_dec_ref(v_e_612_);
lean_dec(v___x_611_);
goto v___jp_663_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
v___x_684_ = l_Lean_MessageData_ofName(v___x_611_);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Lean_indentExpr(v_e_612_);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_Lean_Meta_Sym_reportIssue(v___x_689_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_dec_ref(v___x_690_);
goto v___jp_663_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v___x_662_);
lean_del_object(v___x_656_);
lean_del_object(v___x_637_);
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v___x_662_);
lean_del_object(v___x_656_);
lean_del_object(v___x_637_);
lean_dec_ref(v_e_612_);
lean_dec(v___x_611_);
v_a_699_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_680_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_680_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v___x_707_; 
lean_del_object(v___x_656_);
lean_del_object(v___x_637_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_642_);
lean_ctor_set(v___x_707_, 1, v___x_662_);
v_a_629_ = v___x_707_;
goto v___jp_628_;
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v___x_662_);
lean_del_object(v___x_656_);
lean_del_object(v___x_637_);
lean_dec_ref(v_e_612_);
lean_dec(v___x_611_);
v_a_708_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_677_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_677_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___x_662_);
lean_del_object(v___x_656_);
lean_del_object(v___x_637_);
lean_dec_ref(v_e_612_);
lean_dec(v___x_611_);
v_a_716_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_675_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_675_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
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
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_del_object(v___x_649_);
lean_dec(v_stop_641_);
lean_dec(v_start_640_);
lean_dec_ref(v_array_639_);
lean_del_object(v___x_637_);
lean_dec_ref(v_e_612_);
lean_dec(v___x_611_);
v_a_729_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_653_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_653_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
}
}
v___jp_628_:
{
size_t v___x_630_; size_t v___x_631_; 
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_615_, v___x_630_);
v_i_615_ = v___x_631_;
v_b_616_ = v_a_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object** _args){
lean_object* v___x_743_ = _args[0];
lean_object* v_e_744_ = _args[1];
lean_object* v_as_745_ = _args[2];
lean_object* v_sz_746_ = _args[3];
lean_object* v_i_747_ = _args[4];
lean_object* v_b_748_ = _args[5];
lean_object* v___y_749_ = _args[6];
lean_object* v___y_750_ = _args[7];
lean_object* v___y_751_ = _args[8];
lean_object* v___y_752_ = _args[9];
lean_object* v___y_753_ = _args[10];
lean_object* v___y_754_ = _args[11];
lean_object* v___y_755_ = _args[12];
lean_object* v___y_756_ = _args[13];
lean_object* v___y_757_ = _args[14];
lean_object* v___y_758_ = _args[15];
lean_object* v___y_759_ = _args[16];
_start:
{
size_t v_sz_boxed_760_; size_t v_i_boxed_761_; lean_object* v_res_762_; 
v_sz_boxed_760_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_761_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_743_, v_e_744_, v_as_745_, v_sz_boxed_760_, v_i_boxed_761_, v_b_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v_as_745_);
return v_res_762_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_775_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6));
v___x_776_ = l_Lean_Name_append(v___x_775_, v___x_774_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18));
v___x_797_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17));
v___x_798_ = l_Lean_mkConst(v___x_797_, v___x_796_);
return v___x_798_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21(void){
_start:
{
uint8_t v___x_801_; uint64_t v___x_802_; 
v___x_801_ = 1;
v___x_802_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object* v_e_803_, lean_object* v_thm_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_803_, v___y_805_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_830_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref(v___x_828_);
v___x_830_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_807_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_1171_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_1171_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_1171_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
uint8_t v___x_835_; 
v___x_835_ = lean_nat_dec_lt(v_a_829_, v_a_831_);
lean_dec(v_a_831_);
lean_dec(v_a_829_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
lean_dec_ref(v_thm_804_);
lean_dec_ref(v_e_803_);
v___x_836_ = lean_box(0);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v___x_840_; uint8_t v___x_841_; 
lean_del_object(v___x_833_);
lean_inc_ref(v_e_803_);
v___x_840_ = l_Lean_Expr_cleanupAnnotations(v_e_803_);
v___x_841_ = l_Lean_Expr_isApp(v___x_840_);
if (v___x_841_ == 0)
{
lean_dec_ref(v___x_840_);
lean_dec_ref(v_thm_804_);
lean_dec_ref(v_e_803_);
goto v___jp_825_;
}
else
{
lean_object* v_arg_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_arg_842_ = lean_ctor_get(v___x_840_, 1);
lean_inc_ref(v_arg_842_);
v___x_843_ = l_Lean_Expr_appFnCleanup___redArg(v___x_840_);
v___x_844_ = l_Lean_Expr_isApp(v___x_843_);
if (v___x_844_ == 0)
{
lean_dec_ref(v___x_843_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_thm_804_);
lean_dec_ref(v_e_803_);
goto v___jp_825_;
}
else
{
lean_object* v_arg_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_arg_845_ = lean_ctor_get(v___x_843_, 1);
lean_inc_ref(v_arg_845_);
v___x_846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_843_);
v___x_847_ = l_Lean_Expr_isApp(v___x_846_);
if (v___x_847_ == 0)
{
lean_dec_ref(v___x_846_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_thm_804_);
lean_dec_ref(v_e_803_);
goto v___jp_825_;
}
else
{
lean_object* v_arg_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_arg_848_ = lean_ctor_get(v___x_846_, 1);
lean_inc_ref(v_arg_848_);
v___x_849_ = l_Lean_Expr_appFnCleanup___redArg(v___x_846_);
v___x_850_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1));
v___x_851_ = l_Lean_Expr_isConstOf(v___x_849_, v___x_850_);
lean_dec_ref(v___x_849_);
if (v___x_851_ == 0)
{
lean_dec_ref(v_arg_848_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_thm_804_);
lean_dec_ref(v_e_803_);
goto v___jp_825_;
}
else
{
lean_object* v_declName_852_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_882_; lean_object* v___y_883_; uint8_t v___y_884_; lean_object* v___y_919_; uint8_t v___y_920_; lean_object* v_a_921_; lean_object* v___y_949_; uint8_t v___y_950_; lean_object* v___y_951_; lean_object* v___y_962_; lean_object* v___x_986_; 
v_declName_852_ = lean_ctor_get(v_thm_804_, 0);
lean_inc_n(v_declName_852_, 2);
lean_dec_ref(v_thm_804_);
v___x_986_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_852_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___y_989_; uint8_t v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v_a_1064_; lean_object* v___x_1095_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc_n(v_a_987_, 2);
lean_dec_ref(v___x_986_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
v___x_1095_ = lean_infer_type(v_a_987_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; uint8_t v_foApprox_1098_; uint8_t v_ctxApprox_1099_; uint8_t v_quasiPatternApprox_1100_; uint8_t v_constApprox_1101_; uint8_t v_isDefEqStuckEx_1102_; uint8_t v_unificationHints_1103_; uint8_t v_proofIrrelevance_1104_; uint8_t v_assignSyntheticOpaque_1105_; uint8_t v_offsetCnstrs_1106_; uint8_t v_etaStruct_1107_; uint8_t v_univApprox_1108_; uint8_t v_iota_1109_; uint8_t v_beta_1110_; uint8_t v_proj_1111_; uint8_t v_zeta_1112_; uint8_t v_zetaDelta_1113_; uint8_t v_zetaUnused_1114_; uint8_t v_zetaHave_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1154_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = l_Lean_Meta_Context_config(v___y_811_);
v_foApprox_1098_ = lean_ctor_get_uint8(v___x_1097_, 0);
v_ctxApprox_1099_ = lean_ctor_get_uint8(v___x_1097_, 1);
v_quasiPatternApprox_1100_ = lean_ctor_get_uint8(v___x_1097_, 2);
v_constApprox_1101_ = lean_ctor_get_uint8(v___x_1097_, 3);
v_isDefEqStuckEx_1102_ = lean_ctor_get_uint8(v___x_1097_, 4);
v_unificationHints_1103_ = lean_ctor_get_uint8(v___x_1097_, 5);
v_proofIrrelevance_1104_ = lean_ctor_get_uint8(v___x_1097_, 6);
v_assignSyntheticOpaque_1105_ = lean_ctor_get_uint8(v___x_1097_, 7);
v_offsetCnstrs_1106_ = lean_ctor_get_uint8(v___x_1097_, 8);
v_etaStruct_1107_ = lean_ctor_get_uint8(v___x_1097_, 10);
v_univApprox_1108_ = lean_ctor_get_uint8(v___x_1097_, 11);
v_iota_1109_ = lean_ctor_get_uint8(v___x_1097_, 12);
v_beta_1110_ = lean_ctor_get_uint8(v___x_1097_, 13);
v_proj_1111_ = lean_ctor_get_uint8(v___x_1097_, 14);
v_zeta_1112_ = lean_ctor_get_uint8(v___x_1097_, 15);
v_zetaDelta_1113_ = lean_ctor_get_uint8(v___x_1097_, 16);
v_zetaUnused_1114_ = lean_ctor_get_uint8(v___x_1097_, 17);
v_zetaHave_1115_ = lean_ctor_get_uint8(v___x_1097_, 18);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1117_ = v___x_1097_;
v_isShared_1118_ = v_isSharedCheck_1154_;
goto v_resetjp_1116_;
}
else
{
lean_dec(v___x_1097_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1154_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v_trackZetaDelta_1119_; lean_object* v_zetaDeltaSet_1120_; lean_object* v_lctx_1121_; lean_object* v_localInstances_1122_; lean_object* v_defEqCtx_x3f_1123_; lean_object* v_synthPendingDepth_1124_; lean_object* v_canUnfold_x3f_1125_; uint8_t v_univApprox_1126_; uint8_t v_inTypeClassResolution_1127_; uint8_t v_cacheInferType_1128_; uint8_t v___x_1129_; lean_object* v_config_1131_; 
v_trackZetaDelta_1119_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7);
v_zetaDeltaSet_1120_ = lean_ctor_get(v___y_811_, 1);
v_lctx_1121_ = lean_ctor_get(v___y_811_, 2);
v_localInstances_1122_ = lean_ctor_get(v___y_811_, 3);
v_defEqCtx_x3f_1123_ = lean_ctor_get(v___y_811_, 4);
v_synthPendingDepth_1124_ = lean_ctor_get(v___y_811_, 5);
v_canUnfold_x3f_1125_ = lean_ctor_get(v___y_811_, 6);
v_univApprox_1126_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1127_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 2);
v_cacheInferType_1128_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 3);
v___x_1129_ = 1;
if (v_isShared_1118_ == 0)
{
v_config_1131_ = v___x_1117_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 0, v_foApprox_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 1, v_ctxApprox_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 2, v_quasiPatternApprox_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 3, v_constApprox_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 4, v_isDefEqStuckEx_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 5, v_unificationHints_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 6, v_proofIrrelevance_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 7, v_assignSyntheticOpaque_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 8, v_offsetCnstrs_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 10, v_etaStruct_1107_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 11, v_univApprox_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 12, v_iota_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 13, v_beta_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 14, v_proj_1111_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 15, v_zeta_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 16, v_zetaDelta_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 17, v_zetaUnused_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, 18, v_zetaHave_1115_);
v_config_1131_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
uint64_t v___x_1132_; uint64_t v___x_1133_; uint64_t v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; uint64_t v___x_1137_; uint64_t v___x_1138_; uint64_t v_key_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_ctor_set_uint8(v_config_1131_, 9, v___x_1129_);
v___x_1132_ = l_Lean_Meta_Context_configKey(v___y_811_);
v___x_1133_ = 2ULL;
v___x_1134_ = lean_uint64_shift_right(v___x_1132_, v___x_1133_);
v___x_1135_ = lean_box(0);
v___x_1136_ = 0;
v___x_1137_ = lean_uint64_shift_left(v___x_1134_, v___x_1133_);
v___x_1138_ = lean_uint64_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21);
v_key_1139_ = lean_uint64_lor(v___x_1137_, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1140_, 0, v_config_1131_);
lean_ctor_set_uint64(v___x_1140_, sizeof(void*)*1, v_key_1139_);
lean_inc(v_canUnfold_x3f_1125_);
lean_inc(v_synthPendingDepth_1124_);
lean_inc(v_defEqCtx_x3f_1123_);
lean_inc_ref(v_localInstances_1122_);
lean_inc_ref(v_lctx_1121_);
lean_inc(v_zetaDeltaSet_1120_);
v___x_1141_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v_zetaDeltaSet_1120_);
lean_ctor_set(v___x_1141_, 2, v_lctx_1121_);
lean_ctor_set(v___x_1141_, 3, v_localInstances_1122_);
lean_ctor_set(v___x_1141_, 4, v_defEqCtx_x3f_1123_);
lean_ctor_set(v___x_1141_, 5, v_synthPendingDepth_1124_);
lean_ctor_set(v___x_1141_, 6, v_canUnfold_x3f_1125_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*7, v_trackZetaDelta_1119_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*7 + 1, v_univApprox_1126_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1127_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*7 + 3, v_cacheInferType_1128_);
v___x_1142_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1096_, v___x_1135_, v___x_1136_, v___x_1141_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v___x_1141_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref(v___x_1142_);
v_a_1064_ = v_a_1143_;
goto v___jp_1063_;
}
else
{
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1144_; 
v_a_1144_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v___x_1142_);
v_a_1064_ = v_a_1144_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_arg_848_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_e_803_);
v_a_1145_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1142_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1142_);
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
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_arg_848_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_e_803_);
v_a_1155_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1095_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1095_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
v___jp_988_:
{
if (lean_obj_tag(v___y_993_) == 0)
{
lean_object* v_a_994_; uint8_t v___x_995_; 
v_a_994_ = lean_ctor_get(v___y_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref(v___y_993_);
v___x_995_ = lean_unbox(v_a_994_);
lean_dec(v_a_994_);
if (v___x_995_ == 0)
{
lean_dec_ref(v___y_991_);
lean_dec_ref(v___y_989_);
lean_dec(v_a_987_);
v___y_962_ = v___y_992_;
goto v___jp_961_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; size_t v_sz_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v___y_992_);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = lean_array_get_size(v___y_991_);
v___x_998_ = l_Array_toSubarray___redArg(v___y_991_, v___x_996_, v___x_997_);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
v_sz_1001_ = lean_array_size(v___y_989_);
v___x_1002_ = ((size_t)0ULL);
lean_inc_ref(v_e_803_);
lean_inc(v_declName_852_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_852_, v_e_803_, v___y_989_, v_sz_1001_, v___x_1002_, v___x_1000_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1046_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1046_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1046_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_fst_1008_; 
v_fst_1008_ = lean_ctor_get(v_a_1004_, 0);
lean_inc(v_fst_1008_);
lean_dec(v_a_1004_);
if (lean_obj_tag(v_fst_1008_) == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_a_1011_; lean_object* v___x_1012_; 
lean_del_object(v___x_1006_);
v___x_1009_ = l_Lean_mkAppN(v_a_987_, v___y_989_);
v___x_1010_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_1009_, v___y_812_);
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
lean_inc_ref(v_e_803_);
v___x_1012_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_803_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_809_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1014_);
v___x_1016_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19);
lean_inc_ref(v_e_803_);
v___x_1017_ = l_Lean_mkApp4(v___x_1016_, v_e_803_, v_a_1015_, v_a_1013_, v_a_1011_);
v___x_1018_ = lean_array_get_size(v___y_989_);
v___x_1019_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20));
v___x_1020_ = lean_nat_dec_lt(v___x_996_, v___x_1018_);
if (v___x_1020_ == 0)
{
lean_dec_ref(v___y_989_);
v___y_919_ = v___x_1017_;
v___y_920_ = v___y_990_;
v_a_921_ = v___x_1019_;
goto v___jp_918_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1018_, v___x_1018_);
if (v___x_1021_ == 0)
{
if (v___x_1020_ == 0)
{
lean_dec_ref(v___y_989_);
v___y_919_ = v___x_1017_;
v___y_920_ = v___y_990_;
v_a_921_ = v___x_1019_;
goto v___jp_918_;
}
else
{
size_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_usize_of_nat(v___x_1018_);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_989_, v___x_1002_, v___x_1022_, v___x_1019_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v___y_989_);
v___y_949_ = v___x_1017_;
v___y_950_ = v___y_990_;
v___y_951_ = v___x_1023_;
goto v___jp_948_;
}
}
else
{
size_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_usize_of_nat(v___x_1018_);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_989_, v___x_1002_, v___x_1024_, v___x_1019_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v___y_989_);
v___y_949_ = v___x_1017_;
v___y_950_ = v___y_990_;
v___y_951_ = v___x_1025_;
goto v___jp_948_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_a_1013_);
lean_dec(v_a_1011_);
lean_dec_ref(v___y_989_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_1026_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1014_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1014_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
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
lean_dec(v_a_1011_);
lean_dec_ref(v___y_989_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_1034_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1012_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1012_);
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
lean_object* v_val_1042_; lean_object* v___x_1044_; 
lean_dec_ref(v___y_989_);
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_val_1042_ = lean_ctor_get(v_fst_1008_, 0);
lean_inc(v_val_1042_);
lean_dec_ref(v_fst_1008_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_val_1042_);
v___x_1044_ = v___x_1006_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_val_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v___y_989_);
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_1047_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1003_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1003_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v___y_989_);
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_1055_ = lean_ctor_get(v___y_993_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___y_993_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___y_993_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___y_993_);
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
v___jp_1063_:
{
lean_object* v_snd_1065_; lean_object* v_fst_1066_; lean_object* v_fst_1067_; lean_object* v_snd_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_snd_1065_ = lean_ctor_get(v_a_1064_, 1);
lean_inc(v_snd_1065_);
v_fst_1066_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_fst_1066_);
lean_dec_ref(v_a_1064_);
v_fst_1067_ = lean_ctor_get(v_snd_1065_, 0);
lean_inc(v_fst_1067_);
v_snd_1068_ = lean_ctor_get(v_snd_1065_, 1);
lean_inc_n(v_snd_1068_, 2);
lean_dec(v_snd_1065_);
v___x_1069_ = l_Lean_Expr_cleanupAnnotations(v_snd_1068_);
v___x_1070_ = l_Lean_Expr_isApp(v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec_ref(v___x_1069_);
lean_dec(v_snd_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_fst_1066_);
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_arg_848_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_e_803_);
goto v___jp_822_;
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
lean_dec(v_snd_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_fst_1066_);
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_arg_848_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_e_803_);
goto v___jp_822_;
}
else
{
lean_object* v_arg_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_arg_1074_ = lean_ctor_get(v___x_1072_, 1);
lean_inc_ref(v_arg_1074_);
v___x_1075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1072_);
v___x_1076_ = l_Lean_Expr_isApp(v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec_ref(v___x_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_arg_1071_);
lean_dec(v_snd_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_fst_1066_);
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_arg_848_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_e_803_);
goto v___jp_822_;
}
else
{
lean_object* v_arg_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_arg_1077_ = lean_ctor_get(v___x_1075_, 1);
lean_inc_ref(v_arg_1077_);
v___x_1078_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1075_);
v___x_1079_ = l_Lean_Expr_isConstOf(v___x_1078_, v___x_850_);
lean_dec_ref(v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_arg_1077_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_arg_1071_);
lean_dec(v_snd_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_fst_1066_);
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_arg_848_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_e_803_);
goto v___jp_822_;
}
else
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Meta_isExprDefEq(v_arg_848_, v_arg_1077_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; uint8_t v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
v___x_1082_ = lean_unbox(v_a_1081_);
lean_dec(v_a_1081_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
v___y_989_ = v_fst_1066_;
v___y_990_ = v___x_1079_;
v___y_991_ = v_fst_1067_;
v___y_992_ = v_snd_1068_;
v___y_993_ = v___x_1080_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1083_; 
lean_dec_ref(v___x_1080_);
v___x_1083_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1079_, v_arg_1074_, v_arg_845_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; uint8_t v___x_1085_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = lean_unbox(v_a_1084_);
lean_dec(v_a_1084_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v_arg_1071_);
lean_dec(v_fst_1067_);
lean_dec(v_fst_1066_);
lean_dec(v_a_987_);
lean_dec_ref(v_arg_842_);
v___y_962_ = v_snd_1068_;
goto v___jp_961_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1079_, v_arg_1071_, v_arg_842_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
v___y_989_ = v_fst_1066_;
v___y_990_ = v___x_1079_;
v___y_991_ = v_fst_1067_;
v___y_992_ = v_snd_1068_;
v___y_993_ = v___x_1086_;
goto v___jp_988_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_arg_1071_);
lean_dec(v_snd_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_fst_1066_);
lean_dec(v_a_987_);
lean_dec(v_declName_852_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_e_803_);
v_a_1087_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1083_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1083_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
v___y_989_ = v_fst_1066_;
v___y_990_ = v___x_1079_;
v___y_991_ = v_fst_1067_;
v___y_992_ = v_snd_1068_;
v___y_993_ = v___x_1080_;
goto v___jp_988_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_declName_852_);
lean_dec_ref(v_arg_848_);
lean_dec_ref(v_arg_845_);
lean_dec_ref(v_arg_842_);
lean_dec_ref(v_e_803_);
v_a_1163_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_986_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_986_);
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
v___jp_853_:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_803_, v___y_856_);
lean_dec_ref(v_e_803_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_nat_add(v_a_867_, v___x_868_);
lean_dec(v_a_867_);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v_declName_852_);
v___x_871_ = lean_box(1);
v___x_872_ = l_Lean_Meta_Grind_addNewRawFact(v___y_855_, v___y_854_, v___x_869_, v___x_870_, v___x_871_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
return v___x_872_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v_declName_852_);
v_a_873_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_866_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_866_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
v___jp_881_:
{
if (v___y_884_ == 0)
{
lean_object* v_options_885_; uint8_t v_hasTrace_886_; 
v_options_885_ = lean_ctor_get(v___y_813_, 2);
v_hasTrace_886_ = lean_ctor_get_uint8(v_options_885_, sizeof(void*)*1);
if (v_hasTrace_886_ == 0)
{
v___y_854_ = v___y_883_;
v___y_855_ = v___y_882_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
v___y_864_ = v___y_813_;
v___y_865_ = v___y_814_;
goto v___jp_853_;
}
else
{
lean_object* v_inheritedTraceOptions_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_inheritedTraceOptions_887_ = lean_ctor_get(v___y_813_, 13);
v___x_888_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_889_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7);
v___x_890_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_887_, v_options_885_, v___x_889_);
if (v___x_890_ == 0)
{
v___y_854_ = v___y_883_;
v___y_855_ = v___y_882_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
v___y_864_ = v___y_813_;
v___y_865_ = v___y_814_;
goto v___jp_853_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_inc(v_declName_852_);
v___x_891_ = l_Lean_MessageData_ofName(v_declName_852_);
v___x_892_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
lean_inc_ref(v___y_883_);
v___x_894_ = l_Lean_MessageData_ofExpr(v___y_883_);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_888_, v___x_895_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_dec_ref(v___x_896_);
v___y_854_ = v___y_883_;
v___y_855_ = v___y_882_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
v___y_862_ = v___y_811_;
v___y_863_ = v___y_812_;
v___y_864_ = v___y_813_;
v___y_865_ = v___y_814_;
goto v___jp_853_;
}
else
{
lean_dec_ref(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
return v___x_896_;
}
}
}
}
else
{
lean_object* v___x_897_; 
lean_dec_ref(v___y_883_);
lean_dec_ref(v___y_882_);
v___x_897_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_809_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; uint8_t v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_897_);
v___x_899_ = lean_unbox(v_a_898_);
lean_dec(v_a_898_);
if (v___x_899_ == 0)
{
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
goto v___jp_816_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_900_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_901_ = l_Lean_MessageData_ofName(v_declName_852_);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_indentExpr(v_e_803_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_Meta_Sym_reportIssue(v___x_908_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_dec_ref(v___x_909_);
goto v___jp_816_;
}
else
{
return v___x_909_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_910_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_897_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_897_);
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
}
v___jp_918_:
{
uint8_t v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; 
v___x_922_ = 0;
v___x_923_ = 1;
v___x_924_ = l_Lean_Meta_mkLambdaFVars(v_a_921_, v___y_919_, v___x_922_, v___y_920_, v___x_922_, v___y_920_, v___x_923_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v_a_921_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref(v___x_924_);
v___x_926_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_925_, v___y_812_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc_n(v_a_927_, 2);
lean_dec_ref(v___x_926_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
v___x_928_ = lean_infer_type(v_a_927_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_Expr_hasMVar(v_a_927_);
if (v___x_930_ == 0)
{
uint8_t v___x_931_; 
v___x_931_ = l_Lean_Expr_hasMVar(v_a_929_);
v___y_882_ = v_a_927_;
v___y_883_ = v_a_929_;
v___y_884_ = v___x_931_;
goto v___jp_881_;
}
else
{
v___y_882_ = v_a_927_;
v___y_883_ = v_a_929_;
v___y_884_ = v___y_920_;
goto v___jp_881_;
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_a_927_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_932_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_928_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_928_);
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
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_940_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_924_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_924_);
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
v___jp_948_:
{
if (lean_obj_tag(v___y_951_) == 0)
{
lean_object* v_a_952_; 
v_a_952_ = lean_ctor_get(v___y_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref(v___y_951_);
v___y_919_ = v___y_949_;
v___y_920_ = v___y_950_;
v_a_921_ = v_a_952_;
goto v___jp_918_;
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v___y_949_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_953_ = lean_ctor_get(v___y_951_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___y_951_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___y_951_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___y_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
v___jp_961_:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_809_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; uint8_t v___x_965_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref(v___x_963_);
v___x_965_ = lean_unbox(v_a_964_);
lean_dec(v_a_964_);
if (v___x_965_ == 0)
{
lean_dec_ref(v___y_962_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
goto v___jp_819_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_966_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_967_ = l_Lean_MessageData_ofName(v_declName_852_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_indentExpr(v_e_803_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_indentExpr(v___y_962_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_Meta_Sym_reportIssue(v___x_976_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_dec_ref(v___x_977_);
goto v___jp_819_;
}
else
{
return v___x_977_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v___y_962_);
lean_dec(v_declName_852_);
lean_dec_ref(v_e_803_);
v_a_978_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_963_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_963_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
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
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_829_);
lean_dec_ref(v_thm_804_);
lean_dec_ref(v_e_803_);
v_a_1172_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_830_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_830_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_thm_804_);
lean_dec_ref(v_e_803_);
v_a_1180_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_828_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_828_);
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
v___jp_816_:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_box(0);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
v___jp_819_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
v___jp_822_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_box(0);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
v___jp_825_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_box(0);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object* v_e_1188_, lean_object* v_thm_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(v_e_1188_, v_thm_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec(v___y_1190_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object* v_thm_1202_, lean_object* v_e_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___f_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; 
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed), 13, 2);
lean_closure_set(v___f_1215_, 0, v_e_1203_);
lean_closure_set(v___f_1215_, 1, v_thm_1202_);
v___x_1216_ = 0;
v___x_1217_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v___f_1215_, v___x_1216_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object* v_thm_1218_, lean_object* v_e_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_thm_1218_, v_e_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec(v_a_1220_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object* v_mvarId_1232_, lean_object* v_val_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_1232_, v_val_1233_, v___y_1241_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object* v_mvarId_1246_, lean_object* v_val_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(v_mvarId_1246_, v_val_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object* v_mvarId_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_1260_, v___y_1268_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object* v_mvarId_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(v_mvarId_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec(v_mvarId_1273_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object* v_cls_1286_, lean_object* v_msg_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_1286_, v_msg_1287_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object* v_cls_1300_, lean_object* v_msg_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(v_cls_1300_, v_msg_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v___y_1302_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_1315_, v_x_1316_, v_x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object* v_00_u03b2_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1320_, v_x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_){
_start:
{
uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(v_00_u03b2_1323_, v_x_1324_, v_x_1325_);
lean_dec(v_x_1325_);
lean_dec_ref(v_x_1324_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1328_, lean_object* v_x_1329_, size_t v_x_1330_, size_t v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1329_, v_x_1330_, v_x_1331_, v_x_1332_, v_x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
size_t v_x_217138__boxed_1341_; size_t v_x_217139__boxed_1342_; lean_object* v_res_1343_; 
v_x_217138__boxed_1341_ = lean_unbox_usize(v_x_1337_);
lean_dec(v_x_1337_);
v_x_217139__boxed_1342_ = lean_unbox_usize(v_x_1338_);
lean_dec(v_x_1338_);
v_res_1343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(v_00_u03b2_1335_, v_x_1336_, v_x_217138__boxed_1341_, v_x_217139__boxed_1342_, v_x_1339_, v_x_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1344_, lean_object* v_x_1345_, size_t v_x_1346_, lean_object* v_x_1347_){
_start:
{
uint8_t v___x_1348_; 
v___x_1348_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1345_, v_x_1346_, v_x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
size_t v_x_217155__boxed_1353_; uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_x_217155__boxed_1353_ = lean_unbox_usize(v_x_1351_);
lean_dec(v_x_1351_);
v_res_1354_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(v_00_u03b2_1349_, v_x_1350_, v_x_217155__boxed_1353_, v_x_1352_);
lean_dec(v_x_1352_);
lean_dec_ref(v_x_1350_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03b2_1356_, lean_object* v_n_1357_, lean_object* v_k_1358_, lean_object* v_v_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_n_1357_, v_k_1358_, v_v_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_1361_, size_t v_depth_1362_, lean_object* v_keys_1363_, lean_object* v_vals_1364_, lean_object* v_heq_1365_, lean_object* v_i_1366_, lean_object* v_entries_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_1362_, v_keys_1363_, v_vals_1364_, v_i_1366_, v_entries_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1369_, lean_object* v_depth_1370_, lean_object* v_keys_1371_, lean_object* v_vals_1372_, lean_object* v_heq_1373_, lean_object* v_i_1374_, lean_object* v_entries_1375_){
_start:
{
size_t v_depth_boxed_1376_; lean_object* v_res_1377_; 
v_depth_boxed_1376_ = lean_unbox_usize(v_depth_1370_);
lean_dec(v_depth_1370_);
v_res_1377_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_1369_, v_depth_boxed_1376_, v_keys_1371_, v_vals_1372_, v_heq_1373_, v_i_1374_, v_entries_1375_);
lean_dec_ref(v_vals_1372_);
lean_dec_ref(v_keys_1371_);
return v_res_1377_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_heq_1381_, lean_object* v_i_1382_, lean_object* v_k_1383_){
_start:
{
uint8_t v___x_1384_; 
v___x_1384_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_1379_, v_i_1382_, v_k_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(lean_object* v_00_u03b2_1385_, lean_object* v_keys_1386_, lean_object* v_vals_1387_, lean_object* v_heq_1388_, lean_object* v_i_1389_, lean_object* v_k_1390_){
_start:
{
uint8_t v_res_1391_; lean_object* v_r_1392_; 
v_res_1391_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(v_00_u03b2_1385_, v_keys_1386_, v_vals_1387_, v_heq_1388_, v_i_1389_, v_k_1390_);
lean_dec(v_k_1390_);
lean_dec_ref(v_vals_1387_);
lean_dec_ref(v_keys_1386_);
v_r_1392_ = lean_box(v_res_1391_);
return v_r_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11(lean_object* v_00_u03b2_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_x_1394_, v_x_1395_, v_x_1396_, v_x_1397_);
return v___x_1398_;
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
