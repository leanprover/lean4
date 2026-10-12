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
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getMaxGeneration___redArg(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to apply extensionality theorem `"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\nis not definitionally equal to"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\nresulting terms contain metavariables"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(189, 159, 161, 247, 89, 7, 26, 174)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13;
static const lean_string_object l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_e_31_, v___y_39_);
return v___x_43_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v___y_38_ = stack[7].m_obj;
lean_object* v___y_39_ = stack[8].m_obj;
lean_object* v___y_40_ = stack[9].m_obj;
lean_object* v___y_41_ = stack[10].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___boxed(lean_object* v_e_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(v_e_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec(v___y_46_);
return v_res_57_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(lean_object* v_k_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
lean_inc(v___y_62_);
lean_inc_ref(v___y_61_);
lean_inc(v___y_60_);
lean_inc(v___y_59_);
v___x_70_ = lean_apply_11(v_k_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, lean_box(0));
return v___x_70_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_58_ = stack[0].m_obj;
lean_object* v___y_59_ = stack[1].m_obj;
lean_object* v___y_60_ = stack[2].m_obj;
lean_object* v___y_61_ = stack[3].m_obj;
lean_object* v___y_62_ = stack[4].m_obj;
lean_object* v___y_63_ = stack[5].m_obj;
lean_object* v___y_64_ = stack[6].m_obj;
lean_object* v___y_65_ = stack[7].m_obj;
lean_object* v___y_66_ = stack[8].m_obj;
lean_object* v___y_67_ = stack[9].m_obj;
lean_object* v___y_68_ = stack[10].m_obj;
lean_object* v_res_71_;
v_res_71_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(v_k_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed(lean_object* v_k_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(v_k_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec(v___y_73_);
return v_res_84_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(lean_object* v_k_85_, uint8_t v_allowLevelAssignments_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___f_98_; lean_object* v___x_99_; 
lean_inc(v___y_92_);
lean_inc_ref(v___y_91_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc(v___y_87_);
v___f_98_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_98_, 0, v_k_85_);
lean_closure_set(v___f_98_, 1, v___y_87_);
lean_closure_set(v___f_98_, 2, v___y_88_);
lean_closure_set(v___f_98_, 3, v___y_89_);
lean_closure_set(v___f_98_, 4, v___y_90_);
lean_closure_set(v___f_98_, 5, v___y_91_);
lean_closure_set(v___f_98_, 6, v___y_92_);
v___x_99_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_86_, v___f_98_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
if (lean_obj_tag(v___x_99_) == 0)
{
return v___x_99_;
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_85_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_86_ = stack[1].m_num;
lean_object* v___y_87_ = stack[2].m_obj;
lean_object* v___y_88_ = stack[3].m_obj;
lean_object* v___y_89_ = stack[4].m_obj;
lean_object* v___y_90_ = stack[5].m_obj;
lean_object* v___y_91_ = stack[6].m_obj;
lean_object* v___y_92_ = stack[7].m_obj;
lean_object* v___y_93_ = stack[8].m_obj;
lean_object* v___y_94_ = stack[9].m_obj;
lean_object* v___y_95_ = stack[10].m_obj;
lean_object* v___y_96_ = stack[11].m_obj;
lean_object* v_res_108_;
v_res_108_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_85_, v_allowLevelAssignments_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___boxed(lean_object* v_k_109_, lean_object* v_allowLevelAssignments_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_122_; lean_object* v_res_123_; 
v_allowLevelAssignments_boxed_122_ = lean_unbox(v_allowLevelAssignments_110_);
v_res_123_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_109_, v_allowLevelAssignments_boxed_122_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec(v___y_111_);
return v_res_123_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_object* v_00_u03b1_124_, lean_object* v_k_125_, uint8_t v_allowLevelAssignments_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_125_, v_allowLevelAssignments_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
return v___x_138_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_125_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_126_ = stack[2].m_num;
lean_object* v___y_127_ = stack[3].m_obj;
lean_object* v___y_128_ = stack[4].m_obj;
lean_object* v___y_129_ = stack[5].m_obj;
lean_object* v___y_130_ = stack[6].m_obj;
lean_object* v___y_131_ = stack[7].m_obj;
lean_object* v___y_132_ = stack[8].m_obj;
lean_object* v___y_133_ = stack[9].m_obj;
lean_object* v___y_134_ = stack[10].m_obj;
lean_object* v___y_135_ = stack[11].m_obj;
lean_object* v___y_136_ = stack[12].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_box(0), v_k_125_, v_allowLevelAssignments_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(lean_object* v_00_u03b1_140_, lean_object* v_k_141_, lean_object* v_allowLevelAssignments_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_154_; lean_object* v_res_155_; 
v_allowLevelAssignments_boxed_154_ = lean_unbox(v_allowLevelAssignments_142_);
v_res_155_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(v_00_u03b1_140_, v_k_141_, v_allowLevelAssignments_boxed_154_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec(v___y_143_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12_spec__13___redArg(lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
lean_object* v_ks_160_; lean_object* v_vs_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_185_; 
v_ks_160_ = lean_ctor_get(v_x_156_, 0);
v_vs_161_ = lean_ctor_get(v_x_156_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_185_ == 0)
{
v___x_163_ = v_x_156_;
v_isShared_164_ = v_isSharedCheck_185_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_vs_161_);
lean_inc(v_ks_160_);
lean_dec(v_x_156_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_185_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_array_get_size(v_ks_160_);
v___x_166_ = lean_nat_dec_lt(v_x_157_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
lean_dec(v_x_157_);
v___x_167_ = lean_array_push(v_ks_160_, v_x_158_);
v___x_168_ = lean_array_push(v_vs_161_, v_x_159_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___x_168_);
lean_ctor_set(v___x_163_, 0, v___x_167_);
v___x_170_ = v___x_163_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_object* v_k_x27_172_; uint8_t v___x_173_; 
v_k_x27_172_ = lean_array_fget_borrowed(v_ks_160_, v_x_157_);
v___x_173_ = l_Lean_instBEqMVarId_beq(v_x_158_, v_k_x27_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_175_; 
if (v_isShared_164_ == 0)
{
v___x_175_ = v___x_163_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_ks_160_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_vs_161_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_add(v_x_157_, v___x_176_);
lean_dec(v_x_157_);
v_x_156_ = v___x_175_;
v_x_157_ = v___x_177_;
goto _start;
}
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_180_ = lean_array_fset(v_ks_160_, v_x_157_, v_x_158_);
v___x_181_ = lean_array_fset(v_vs_161_, v_x_157_, v_x_159_);
lean_dec(v_x_157_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___x_181_);
lean_ctor_set(v___x_163_, 0, v___x_180_);
v___x_183_ = v___x_163_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12___redArg(lean_object* v_n_186_, lean_object* v_k_187_, lean_object* v_v_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12_spec__13___redArg(v_n_186_, v___x_189_, v_k_187_, v_v_188_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_191_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(lean_object* v_x_192_, size_t v_x_193_, size_t v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v_es_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v_j_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_es_197_ = lean_ctor_get(v_x_192_, 0);
v___x_198_ = ((size_t)31ULL);
v___x_199_ = lean_usize_land(v_x_193_, v___x_198_);
v_j_200_ = lean_usize_to_nat(v___x_199_);
v___x_201_ = lean_array_get_size(v_es_197_);
v___x_202_ = lean_nat_dec_lt(v_j_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_dec(v_j_200_);
lean_dec(v_x_196_);
lean_dec(v_x_195_);
return v_x_192_;
}
else
{
lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_241_; 
lean_inc_ref(v_es_197_);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v_x_192_, 0);
lean_dec(v_unused_242_);
v___x_204_ = v_x_192_;
v_isShared_205_ = v_isSharedCheck_241_;
goto v_resetjp_203_;
}
else
{
lean_dec(v_x_192_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_241_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_v_206_; lean_object* v___x_207_; lean_object* v_xs_x27_208_; lean_object* v___y_210_; 
v_v_206_ = lean_array_fget(v_es_197_, v_j_200_);
v___x_207_ = lean_box(0);
v_xs_x27_208_ = lean_array_fset(v_es_197_, v_j_200_, v___x_207_);
switch(lean_obj_tag(v_v_206_))
{
case 0:
{
lean_object* v_key_215_; lean_object* v_val_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_226_; 
v_key_215_ = lean_ctor_get(v_v_206_, 0);
v_val_216_ = lean_ctor_get(v_v_206_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_v_206_);
if (v_isSharedCheck_226_ == 0)
{
v___x_218_ = v_v_206_;
v_isShared_219_ = v_isSharedCheck_226_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_val_216_);
lean_inc(v_key_215_);
lean_dec(v_v_206_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_226_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
uint8_t v___x_220_; 
v___x_220_ = l_Lean_instBEqMVarId_beq(v_x_195_, v_key_215_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_del_object(v___x_218_);
v___x_221_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_215_, v_val_216_, v_x_195_, v_x_196_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___y_210_ = v___x_222_;
goto v___jp_209_;
}
else
{
lean_object* v___x_224_; 
lean_dec(v_val_216_);
lean_dec(v_key_215_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v_x_196_);
lean_ctor_set(v___x_218_, 0, v_x_195_);
v___x_224_ = v___x_218_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_x_195_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_x_196_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
v___y_210_ = v___x_224_;
goto v___jp_209_;
}
}
}
}
case 1:
{
lean_object* v_node_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_239_; 
v_node_227_ = lean_ctor_get(v_v_206_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_v_206_);
if (v_isSharedCheck_239_ == 0)
{
v___x_229_ = v_v_206_;
v_isShared_230_ = v_isSharedCheck_239_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_node_227_);
lean_dec(v_v_206_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_239_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
size_t v___x_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_231_ = ((size_t)5ULL);
v___x_232_ = lean_usize_shift_right(v_x_193_, v___x_231_);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_x_194_, v___x_233_);
v___x_235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_node_227_, v___x_232_, v___x_234_, v_x_195_, v_x_196_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_235_);
v___x_237_ = v___x_229_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
v___y_210_ = v___x_237_;
goto v___jp_209_;
}
}
}
default: 
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_x_195_);
lean_ctor_set(v___x_240_, 1, v_x_196_);
v___y_210_ = v___x_240_;
goto v___jp_209_;
}
}
v___jp_209_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_array_fset(v_xs_x27_208_, v_j_200_, v___y_210_);
lean_dec(v_j_200_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_211_);
v___x_213_ = v___x_204_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
else
{
lean_object* v_ks_243_; lean_object* v_vs_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_262_; 
v_ks_243_ = lean_ctor_get(v_x_192_, 0);
v_vs_244_ = lean_ctor_get(v_x_192_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_262_ == 0)
{
v___x_246_ = v_x_192_;
v_isShared_247_ = v_isSharedCheck_262_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_vs_244_);
lean_inc(v_ks_243_);
lean_dec(v_x_192_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_262_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_ks_243_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_vs_244_);
v___x_249_ = v_reuseFailAlloc_261_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v_newNode_250_; size_t v___x_251_; uint8_t v___x_252_; 
v_newNode_250_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12___redArg(v___x_249_, v_x_195_, v_x_196_);
v___x_251_ = ((size_t)7ULL);
v___x_252_ = lean_usize_dec_le(v___x_251_, v_x_194_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_253_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_250_);
v___x_254_ = lean_unsigned_to_nat(4u);
v___x_255_ = lean_nat_dec_lt(v___x_253_, v___x_254_);
lean_dec(v___x_253_);
if (v___x_255_ == 0)
{
lean_object* v_ks_256_; lean_object* v_vs_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_ks_256_ = lean_ctor_get(v_newNode_250_, 0);
lean_inc_ref(v_ks_256_);
v_vs_257_ = lean_ctor_get(v_newNode_250_, 1);
lean_inc_ref(v_vs_257_);
lean_dec_ref(v_newNode_250_);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_x_194_, v_ks_256_, v_vs_257_, v___x_258_, v___x_259_);
lean_dec_ref(v_vs_257_);
lean_dec_ref(v_ks_256_);
return v___x_260_;
}
else
{
return v_newNode_250_;
}
}
else
{
return v_newNode_250_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_192_ = stack[0].m_obj;
size_t v_x_193_ = stack[1].m_num;
size_t v_x_194_ = stack[2].m_num;
lean_object* v_x_195_ = stack[3].m_obj;
lean_object* v_x_196_ = stack[4].m_obj;
lean_object* v_res_263_;
v_res_263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_192_, v_x_193_, v_x_194_, v_x_195_, v_x_196_);
stack->m_obj
 = v_res_263_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(size_t v_depth_264_, lean_object* v_keys_265_, lean_object* v_vals_266_, lean_object* v_i_267_, lean_object* v_entries_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_array_get_size(v_keys_265_);
v___x_270_ = lean_nat_dec_lt(v_i_267_, v___x_269_);
if (v___x_270_ == 0)
{
lean_dec(v_i_267_);
return v_entries_268_;
}
else
{
lean_object* v_k_271_; lean_object* v_v_272_; uint64_t v___x_273_; size_t v_h_274_; size_t v___x_275_; lean_object* v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v_h_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_k_271_ = lean_array_fget_borrowed(v_keys_265_, v_i_267_);
v_v_272_ = lean_array_fget_borrowed(v_vals_266_, v_i_267_);
v___x_273_ = l_Lean_instHashableMVarId_hash(v_k_271_);
v_h_274_ = lean_uint64_to_usize(v___x_273_);
v___x_275_ = ((size_t)5ULL);
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_sub(v_depth_264_, v___x_277_);
v___x_279_ = lean_usize_mul(v___x_275_, v___x_278_);
v_h_280_ = lean_usize_shift_right(v_h_274_, v___x_279_);
v___x_281_ = lean_nat_add(v_i_267_, v___x_276_);
lean_dec(v_i_267_);
lean_inc(v_v_272_);
lean_inc(v_k_271_);
v___x_282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_entries_268_, v_h_280_, v_depth_264_, v_k_271_, v_v_272_);
v_i_267_ = v___x_281_;
v_entries_268_ = v___x_282_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_264_ = stack[0].m_num;
lean_object* v_keys_265_ = stack[1].m_obj;
lean_object* v_vals_266_ = stack[2].m_obj;
lean_object* v_i_267_ = stack[3].m_obj;
lean_object* v_entries_268_ = stack[4].m_obj;
lean_object* v_res_284_;
v_res_284_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_depth_264_, v_keys_265_, v_vals_266_, v_i_267_, v_entries_268_);
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_depth_285_, lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_entries_289_){
_start:
{
size_t v_depth_boxed_290_; lean_object* v_res_291_; 
v_depth_boxed_290_ = lean_unbox_usize(v_depth_285_);
lean_dec(v_depth_285_);
v_res_291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_depth_boxed_290_, v_keys_286_, v_vals_287_, v_i_288_, v_entries_289_);
lean_dec_ref(v_vals_287_);
lean_dec_ref(v_keys_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
size_t v_x_145063__boxed_297_; size_t v_x_145064__boxed_298_; lean_object* v_res_299_; 
v_x_145063__boxed_297_ = lean_unbox_usize(v_x_293_);
lean_dec(v_x_293_);
v_x_145064__boxed_298_ = lean_unbox_usize(v_x_294_);
lean_dec(v_x_294_);
v_res_299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_292_, v_x_145063__boxed_297_, v_x_145064__boxed_298_, v_x_295_, v_x_296_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
uint64_t v___x_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___x_303_ = l_Lean_instHashableMVarId_hash(v_x_301_);
v___x_304_ = lean_uint64_to_usize(v___x_303_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_300_, v___x_304_, v___x_305_, v_x_301_, v_x_302_);
return v___x_306_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object* v_mvarId_307_, lean_object* v_val_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_mctx_312_; lean_object* v_cache_313_; lean_object* v_zetaDeltaFVarIds_314_; lean_object* v_postponed_315_; lean_object* v_diag_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_346_; 
v___x_311_ = lean_st_ref_take(v___y_309_);
v_mctx_312_ = lean_ctor_get(v___x_311_, 0);
v_cache_313_ = lean_ctor_get(v___x_311_, 1);
v_zetaDeltaFVarIds_314_ = lean_ctor_get(v___x_311_, 2);
v_postponed_315_ = lean_ctor_get(v___x_311_, 3);
v_diag_316_ = lean_ctor_get(v___x_311_, 4);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_346_ == 0)
{
v___x_318_ = v___x_311_;
v_isShared_319_ = v_isSharedCheck_346_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_diag_316_);
lean_inc(v_postponed_315_);
lean_inc(v_zetaDeltaFVarIds_314_);
lean_inc(v_cache_313_);
lean_inc(v_mctx_312_);
lean_dec(v___x_311_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_346_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_depth_320_; lean_object* v_levelAssignDepth_321_; lean_object* v_lmvarCounter_322_; lean_object* v_mvarCounter_323_; lean_object* v_lDecls_324_; lean_object* v_decls_325_; lean_object* v_userNames_326_; lean_object* v_lAssignment_327_; lean_object* v_eAssignment_328_; lean_object* v_dAssignment_329_; lean_object* v_instanceTypedMVars_330_; lean_object* v_synthNormMemo_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_345_; 
v_depth_320_ = lean_ctor_get(v_mctx_312_, 0);
v_levelAssignDepth_321_ = lean_ctor_get(v_mctx_312_, 1);
v_lmvarCounter_322_ = lean_ctor_get(v_mctx_312_, 2);
v_mvarCounter_323_ = lean_ctor_get(v_mctx_312_, 3);
v_lDecls_324_ = lean_ctor_get(v_mctx_312_, 4);
v_decls_325_ = lean_ctor_get(v_mctx_312_, 5);
v_userNames_326_ = lean_ctor_get(v_mctx_312_, 6);
v_lAssignment_327_ = lean_ctor_get(v_mctx_312_, 7);
v_eAssignment_328_ = lean_ctor_get(v_mctx_312_, 8);
v_dAssignment_329_ = lean_ctor_get(v_mctx_312_, 9);
v_instanceTypedMVars_330_ = lean_ctor_get(v_mctx_312_, 10);
v_synthNormMemo_331_ = lean_ctor_get(v_mctx_312_, 11);
v_isSharedCheck_345_ = !lean_is_exclusive(v_mctx_312_);
if (v_isSharedCheck_345_ == 0)
{
v___x_333_ = v_mctx_312_;
v_isShared_334_ = v_isSharedCheck_345_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_synthNormMemo_331_);
lean_inc(v_instanceTypedMVars_330_);
lean_inc(v_dAssignment_329_);
lean_inc(v_eAssignment_328_);
lean_inc(v_lAssignment_327_);
lean_inc(v_userNames_326_);
lean_inc(v_decls_325_);
lean_inc(v_lDecls_324_);
lean_inc(v_mvarCounter_323_);
lean_inc(v_lmvarCounter_322_);
lean_inc(v_levelAssignDepth_321_);
lean_inc(v_depth_320_);
lean_dec(v_mctx_312_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_345_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_335_ = lean_box(0);
v___x_336_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_328_, v_mvarId_307_, v_val_308_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 8, v___x_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_depth_320_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_levelAssignDepth_321_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_lmvarCounter_322_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_mvarCounter_323_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v_lDecls_324_);
lean_ctor_set(v_reuseFailAlloc_344_, 5, v_decls_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 6, v_userNames_326_);
lean_ctor_set(v_reuseFailAlloc_344_, 7, v_lAssignment_327_);
lean_ctor_set(v_reuseFailAlloc_344_, 8, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_344_, 9, v_dAssignment_329_);
lean_ctor_set(v_reuseFailAlloc_344_, 10, v_instanceTypedMVars_330_);
lean_ctor_set(v_reuseFailAlloc_344_, 11, v_synthNormMemo_331_);
v___x_338_ = v_reuseFailAlloc_344_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_338_);
v___x_340_ = v___x_318_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_cache_313_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_zetaDeltaFVarIds_314_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_postponed_315_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_diag_316_);
v___x_340_ = v_reuseFailAlloc_343_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_st_ref_put(v___y_309_, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_335_);
return v___x_342_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_307_ = stack[0].m_obj;
lean_object* v_val_308_ = stack[1].m_obj;
lean_object* v___y_309_ = stack[2].m_obj;
lean_object* v_res_347_;
v_res_347_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_307_, v_val_308_, v___y_309_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object* v_mvarId_348_, lean_object* v_val_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_348_, v_val_349_, v___y_350_);
lean_dec(v___y_350_);
return v_res_352_;
}
}
lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(uint8_t v___x_353_, lean_object* v_p_354_, lean_object* v_e_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = l_Lean_Expr_isMVar(v_p_354_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_isExprDefEq(v_p_354_, v_e_355_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v___x_369_ = l_Lean_Expr_mvarId_x21(v_p_354_);
lean_dec_ref(v_p_354_);
v___x_370_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_369_, v_e_355_, v___y_363_);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_379_);
v___x_372_ = v___x_370_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_370_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_box(v___x_353_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_instantiateExtTheorem___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_353_ = stack[0].m_num;
lean_object* v_p_354_ = stack[1].m_obj;
lean_object* v_e_355_ = stack[2].m_obj;
lean_object* v___y_356_ = stack[3].m_obj;
lean_object* v___y_357_ = stack[4].m_obj;
lean_object* v___y_358_ = stack[5].m_obj;
lean_object* v___y_359_ = stack[6].m_obj;
lean_object* v___y_360_ = stack[7].m_obj;
lean_object* v___y_361_ = stack[8].m_obj;
lean_object* v___y_362_ = stack[9].m_obj;
lean_object* v___y_363_ = stack[10].m_obj;
lean_object* v___y_364_ = stack[11].m_obj;
lean_object* v___y_365_ = stack[12].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_353_, v_p_354_, v_e_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object* v___x_381_, lean_object* v_p_382_, lean_object* v_e_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v___x_145386__boxed_395_; lean_object* v_res_396_; 
v___x_145386__boxed_395_ = lean_unbox(v___x_381_);
v_res_396_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_145386__boxed_395_, v_p_382_, v_e_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v___y_384_);
return v_res_396_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(lean_object* v_msgData_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; lean_object* v_env_404_; uint8_t v___x_405_; lean_object* v_env_406_; lean_object* v___x_407_; lean_object* v_toCold_408_; lean_object* v_mctx_409_; lean_object* v_lctx_410_; lean_object* v_options_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_403_ = lean_st_ref_get(v___y_401_);
v_env_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_env_404_);
lean_dec(v___x_403_);
v___x_405_ = 0;
v_env_406_ = l_Lean_Environment_setRecordingDeps(v_env_404_, v___x_405_);
v___x_407_ = lean_st_ref_get(v___y_399_);
v_toCold_408_ = lean_ctor_get(v___y_400_, 0);
v_mctx_409_ = lean_ctor_get(v___x_407_, 0);
lean_inc_ref(v_mctx_409_);
lean_dec(v___x_407_);
v_lctx_410_ = lean_ctor_get(v___y_398_, 2);
v_options_411_ = lean_ctor_get(v_toCold_408_, 2);
lean_inc_ref(v_options_411_);
lean_inc_ref(v_lctx_410_);
v___x_412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_412_, 0, v_env_406_);
lean_ctor_set(v___x_412_, 1, v_mctx_409_);
lean_ctor_set(v___x_412_, 2, v_lctx_410_);
lean_ctor_set(v___x_412_, 3, v_options_411_);
v___x_413_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_msgData_397_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_397_ = stack[0].m_obj;
lean_object* v___y_398_ = stack[1].m_obj;
lean_object* v___y_399_ = stack[2].m_obj;
lean_object* v___y_400_ = stack[3].m_obj;
lean_object* v___y_401_ = stack[4].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msgData_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6___boxed(lean_object* v_msgData_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msgData_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_422_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_423_; double v___x_424_; 
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_float_of_nat(v___x_423_);
return v___x_424_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object* v_cls_428_, lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_ref_435_; lean_object* v___x_436_; lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_482_; 
v_ref_435_ = lean_ctor_get(v___y_432_, 2);
v___x_436_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msg_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_482_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_482_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_482_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_traceState_442_; lean_object* v_env_443_; lean_object* v_nextMacroScope_444_; lean_object* v_ngen_445_; lean_object* v_auxDeclNGen_446_; lean_object* v_cache_447_; lean_object* v_recordedDeps_448_; lean_object* v_messages_449_; lean_object* v_infoState_450_; lean_object* v_snapshotTasks_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_481_; 
v___x_441_ = lean_st_ref_take(v___y_433_);
v_traceState_442_ = lean_ctor_get(v___x_441_, 4);
v_env_443_ = lean_ctor_get(v___x_441_, 0);
v_nextMacroScope_444_ = lean_ctor_get(v___x_441_, 1);
v_ngen_445_ = lean_ctor_get(v___x_441_, 2);
v_auxDeclNGen_446_ = lean_ctor_get(v___x_441_, 3);
v_cache_447_ = lean_ctor_get(v___x_441_, 5);
v_recordedDeps_448_ = lean_ctor_get(v___x_441_, 6);
v_messages_449_ = lean_ctor_get(v___x_441_, 7);
v_infoState_450_ = lean_ctor_get(v___x_441_, 8);
v_snapshotTasks_451_ = lean_ctor_get(v___x_441_, 9);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_481_ == 0)
{
v___x_453_ = v___x_441_;
v_isShared_454_ = v_isSharedCheck_481_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_snapshotTasks_451_);
lean_inc(v_infoState_450_);
lean_inc(v_messages_449_);
lean_inc(v_recordedDeps_448_);
lean_inc(v_cache_447_);
lean_inc(v_traceState_442_);
lean_inc(v_auxDeclNGen_446_);
lean_inc(v_ngen_445_);
lean_inc(v_nextMacroScope_444_);
lean_inc(v_env_443_);
lean_dec(v___x_441_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_481_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
uint64_t v_tid_455_; lean_object* v_traces_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_480_; 
v_tid_455_ = lean_ctor_get_uint64(v_traceState_442_, sizeof(void*)*1);
v_traces_456_ = lean_ctor_get(v_traceState_442_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_traceState_442_);
if (v_isSharedCheck_480_ == 0)
{
v___x_458_ = v_traceState_442_;
v_isShared_459_ = v_isSharedCheck_480_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_traces_456_);
lean_dec(v_traceState_442_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_480_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_461_; double v___x_462_; uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_460_ = lean_box(0);
v___x_461_ = lean_box(0);
v___x_462_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0);
v___x_463_ = 0;
v___x_464_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
v___x_465_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_465_, 0, v_cls_428_);
lean_ctor_set(v___x_465_, 1, v___x_461_);
lean_ctor_set(v___x_465_, 2, v___x_464_);
lean_ctor_set_float(v___x_465_, sizeof(void*)*3, v___x_462_);
lean_ctor_set_float(v___x_465_, sizeof(void*)*3 + 8, v___x_462_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*3 + 16, v___x_463_);
v___x_466_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2));
v___x_467_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v_a_437_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_inc(v_ref_435_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_ref_435_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Lean_PersistentArray_push___redArg(v_traces_456_, v___x_468_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_469_);
v___x_471_ = v___x_458_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_469_);
lean_ctor_set_uint64(v_reuseFailAlloc_479_, sizeof(void*)*1, v_tid_455_);
v___x_471_ = v_reuseFailAlloc_479_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v___x_471_);
v___x_473_ = v___x_453_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_env_443_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_nextMacroScope_444_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_ngen_445_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_auxDeclNGen_446_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v_cache_447_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v_recordedDeps_448_);
lean_ctor_set(v_reuseFailAlloc_478_, 7, v_messages_449_);
lean_ctor_set(v_reuseFailAlloc_478_, 8, v_infoState_450_);
lean_ctor_set(v_reuseFailAlloc_478_, 9, v_snapshotTasks_451_);
v___x_473_ = v_reuseFailAlloc_478_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_st_ref_put(v___y_433_, v___x_473_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_460_);
v___x_476_ = v___x_439_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_460_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_428_ = stack[0].m_obj;
lean_object* v_msg_429_ = stack[1].m_obj;
lean_object* v___y_430_ = stack[2].m_obj;
lean_object* v___y_431_ = stack[3].m_obj;
lean_object* v___y_432_ = stack[4].m_obj;
lean_object* v___y_433_ = stack[5].m_obj;
lean_object* v_res_483_;
v_res_483_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_428_, v_msg_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object* v_cls_484_, lean_object* v_msg_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_484_, v_msg_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_491_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_keys_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_array_get_size(v_keys_492_);
v___x_496_ = lean_nat_dec_lt(v_i_493_, v___x_495_);
if (v___x_496_ == 0)
{
lean_dec(v_i_493_);
return v___x_496_;
}
else
{
lean_object* v_k_x27_497_; uint8_t v___x_498_; 
v_k_x27_497_ = lean_array_fget_borrowed(v_keys_492_, v_i_493_);
v___x_498_ = l_Lean_instBEqMVarId_beq(v_k_494_, v_k_x27_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_i_493_, v___x_499_);
lean_dec(v_i_493_);
v_i_493_ = v___x_500_;
goto _start;
}
else
{
lean_dec(v_i_493_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_492_ = stack[0].m_obj;
lean_object* v_i_493_ = stack[1].m_obj;
lean_object* v_k_494_ = stack[2].m_obj;
uint8_t v_res_502_;
v_res_502_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_keys_492_, v_i_493_, v_k_494_);
stack->m_num = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object* v_keys_503_, lean_object* v_i_504_, lean_object* v_k_505_){
_start:
{
uint8_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_keys_503_, v_i_504_, v_k_505_);
lean_dec(v_k_505_);
lean_dec_ref(v_keys_503_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(lean_object* v_x_508_, size_t v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v_es_511_; lean_object* v___x_512_; size_t v___x_513_; size_t v___x_514_; lean_object* v_j_515_; lean_object* v___x_516_; 
v_es_511_ = lean_ctor_get(v_x_508_, 0);
v___x_512_ = lean_box(2);
v___x_513_ = ((size_t)31ULL);
v___x_514_ = lean_usize_land(v_x_509_, v___x_513_);
v_j_515_ = lean_usize_to_nat(v___x_514_);
v___x_516_ = lean_array_get_borrowed(v___x_512_, v_es_511_, v_j_515_);
lean_dec(v_j_515_);
switch(lean_obj_tag(v___x_516_))
{
case 0:
{
lean_object* v_key_517_; uint8_t v___x_518_; 
v_key_517_ = lean_ctor_get(v___x_516_, 0);
v___x_518_ = l_Lean_instBEqMVarId_beq(v_x_510_, v_key_517_);
return v___x_518_;
}
case 1:
{
lean_object* v_node_519_; size_t v___x_520_; size_t v___x_521_; 
v_node_519_ = lean_ctor_get(v___x_516_, 0);
v___x_520_ = ((size_t)5ULL);
v___x_521_ = lean_usize_shift_right(v_x_509_, v___x_520_);
v_x_508_ = v_node_519_;
v_x_509_ = v___x_521_;
goto _start;
}
default: 
{
uint8_t v___x_523_; 
v___x_523_ = 0;
return v___x_523_;
}
}
}
else
{
lean_object* v_ks_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_ks_524_ = lean_ctor_get(v_x_508_, 0);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_ks_524_, v___x_525_, v_x_510_);
return v___x_526_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_508_ = stack[0].m_obj;
size_t v_x_509_ = stack[1].m_num;
lean_object* v_x_510_ = stack[2].m_obj;
uint8_t v_res_527_;
v_res_527_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_508_, v_x_509_, v_x_510_);
stack->m_num = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
size_t v_x_145700__boxed_531_; uint8_t v_res_532_; lean_object* v_r_533_; 
v_x_145700__boxed_531_ = lean_unbox_usize(v_x_529_);
lean_dec(v_x_529_);
v_res_532_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_528_, v_x_145700__boxed_531_, v_x_530_);
lean_dec(v_x_530_);
lean_dec_ref(v_x_528_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
uint64_t v___x_536_; size_t v___x_537_; uint8_t v___x_538_; 
v___x_536_ = l_Lean_instHashableMVarId_hash(v_x_535_);
v___x_537_ = lean_uint64_to_usize(v___x_536_);
v___x_538_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_534_, v___x_537_, v_x_535_);
return v___x_538_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_534_ = stack[0].m_obj;
lean_object* v_x_535_ = stack[1].m_obj;
uint8_t v_res_539_;
v_res_539_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_534_, v_x_535_);
stack->m_num = v_res_539_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_540_, v_x_541_);
lean_dec(v_x_541_);
lean_dec_ref(v_x_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object* v_mvarId_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; lean_object* v_mctx_548_; lean_object* v_eAssignment_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_547_ = lean_st_ref_get(v___y_545_);
v_mctx_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_mctx_548_);
lean_dec(v___x_547_);
v_eAssignment_549_ = lean_ctor_get(v_mctx_548_, 8);
lean_inc_ref(v_eAssignment_549_);
lean_dec_ref(v_mctx_548_);
v___x_550_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_eAssignment_549_, v_mvarId_544_);
lean_dec_ref(v_eAssignment_549_);
v___x_551_ = lean_box(v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_544_ = stack[0].m_obj;
lean_object* v___y_545_ = stack[1].m_obj;
lean_object* v_res_553_;
v_res_553_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_544_, v___y_545_);
stack->m_obj
 = v_res_553_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object* v_mvarId_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec(v_mvarId_554_);
return v_res_557_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object* v_as_558_, size_t v_i_559_, size_t v_stop_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_a_574_; uint8_t v___x_578_; 
v___x_578_ = lean_usize_dec_eq(v_i_559_, v_stop_560_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_579_ = lean_array_uget_borrowed(v_as_558_, v_i_559_);
v___x_582_ = l_Lean_Expr_mvarId_x21(v___x_579_);
v___x_583_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_582_, v___y_569_);
lean_dec(v___x_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; uint8_t v___x_585_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = lean_unbox(v_a_584_);
lean_dec(v_a_584_);
if (v___x_585_ == 0)
{
goto v___jp_580_;
}
else
{
v_a_574_ = v_b_561_;
goto v___jp_573_;
}
}
else
{
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_586_; uint8_t v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_583_, 1);
v___x_587_ = lean_unbox(v_a_586_);
lean_dec(v_a_586_);
if (v___x_587_ == 0)
{
v_a_574_ = v_b_561_;
goto v___jp_573_;
}
else
{
goto v___jp_580_;
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_b_561_);
v_a_588_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_583_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_583_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
v___jp_580_:
{
lean_object* v___x_581_; 
lean_inc(v___x_579_);
v___x_581_ = lean_array_push(v_b_561_, v___x_579_);
v_a_574_ = v___x_581_;
goto v___jp_573_;
}
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_b_561_);
return v___x_596_;
}
v___jp_573_:
{
size_t v___x_575_; size_t v___x_576_; 
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_559_, v___x_575_);
v_i_559_ = v___x_576_;
v_b_561_ = v_a_574_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_558_ = stack[0].m_obj;
size_t v_i_559_ = stack[1].m_num;
size_t v_stop_560_ = stack[2].m_num;
lean_object* v_b_561_ = stack[3].m_obj;
lean_object* v___y_562_ = stack[4].m_obj;
lean_object* v___y_563_ = stack[5].m_obj;
lean_object* v___y_564_ = stack[6].m_obj;
lean_object* v___y_565_ = stack[7].m_obj;
lean_object* v___y_566_ = stack[8].m_obj;
lean_object* v___y_567_ = stack[9].m_obj;
lean_object* v___y_568_ = stack[10].m_obj;
lean_object* v___y_569_ = stack[11].m_obj;
lean_object* v___y_570_ = stack[12].m_obj;
lean_object* v___y_571_ = stack[13].m_obj;
lean_object* v_res_597_;
v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_558_, v_i_559_, v_stop_560_, v_b_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_stop_600_, lean_object* v_b_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
size_t v_i_boxed_613_; size_t v_stop_boxed_614_; lean_object* v_res_615_; 
v_i_boxed_613_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_stop_boxed_614_ = lean_unbox_usize(v_stop_600_);
lean_dec(v_stop_600_);
v_res_615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_598_, v_i_boxed_613_, v_stop_boxed_614_, v_b_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v_as_598_);
return v_res_615_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1));
v___x_620_ = l_Lean_stringToMessageData(v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3));
v___x_623_ = l_Lean_stringToMessageData(v___x_622_);
return v___x_623_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object* v___x_624_, lean_object* v_e_625_, lean_object* v_as_626_, size_t v_sz_627_, size_t v_i_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_a_642_; uint8_t v___x_646_; 
v___x_646_ = lean_usize_dec_lt(v_i_628_, v_sz_627_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec_ref(v_e_625_);
lean_dec(v___x_624_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v_b_629_);
return v___x_647_;
}
else
{
lean_object* v_snd_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_747_; 
v_snd_648_ = lean_ctor_get(v_b_629_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_b_629_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_b_629_, 0);
lean_dec(v_unused_748_);
v___x_650_ = v_b_629_;
v_isShared_651_ = v_isSharedCheck_747_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_snd_648_);
lean_dec(v_b_629_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_747_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_array_652_; lean_object* v_start_653_; lean_object* v_stop_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_array_652_ = lean_ctor_get(v_snd_648_, 0);
v_start_653_ = lean_ctor_get(v_snd_648_, 1);
v_stop_654_ = lean_ctor_get(v_snd_648_, 2);
v___x_655_ = lean_box(0);
v___x_656_ = lean_nat_dec_lt(v_start_653_, v_stop_654_);
if (v___x_656_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_e_625_);
lean_dec(v___x_624_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_655_);
v___x_658_ = v___x_650_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_snd_648_);
v___x_658_ = v_reuseFailAlloc_660_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
else
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_743_; 
lean_inc(v_stop_654_);
lean_inc(v_start_653_);
lean_inc_ref(v_array_652_);
v_isSharedCheck_743_ = !lean_is_exclusive(v_snd_648_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; 
v_unused_744_ = lean_ctor_get(v_snd_648_, 2);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_snd_648_, 1);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_snd_648_, 0);
lean_dec(v_unused_746_);
v___x_662_ = v_snd_648_;
v_isShared_663_ = v_isSharedCheck_743_;
goto v_resetjp_661_;
}
else
{
lean_dec(v_snd_648_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_743_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_a_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v_a_664_ = lean_array_uget_borrowed(v_as_626_, v_i_628_);
v___x_665_ = lean_array_fget(v_array_652_, v_start_653_);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_add(v_start_653_, v___x_666_);
lean_dec(v_start_653_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_667_);
v___x_669_ = v___x_662_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_array_652_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_stop_654_);
v___x_669_ = v_reuseFailAlloc_742_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = l_Lean_Expr_mvarId_x21(v_a_664_);
v___x_677_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_676_, v___y_637_);
lean_dec(v___x_676_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; uint8_t v___x_731_; uint8_t v___x_732_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v___x_731_ = lean_unbox(v___x_665_);
lean_dec(v___x_665_);
v___x_732_ = l_Lean_BinderInfo_isInstImplicit(v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v_a_678_);
if (v___x_732_ == 0)
{
lean_del_object(v___x_650_);
goto v___jp_729_;
}
else
{
goto v___jp_679_;
}
}
else
{
uint8_t v___x_733_; 
v___x_733_ = lean_unbox(v_a_678_);
lean_dec(v_a_678_);
if (v___x_733_ == 0)
{
goto v___jp_679_;
}
else
{
lean_del_object(v___x_650_);
goto v___jp_729_;
}
}
v___jp_679_:
{
lean_object* v___x_680_; 
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v_a_664_);
v___x_680_ = lean_infer_type(v_a_664_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
lean_inc(v_a_664_);
v___x_682_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_a_664_, v_a_681_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; uint8_t v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = lean_unbox(v_a_683_);
lean_dec(v_a_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
v___x_686_ = l_Lean_MessageData_ofName(v___x_624_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_Lean_indentExpr(v_e_625_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_634_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; uint8_t v_verbose_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v_verbose_694_ = lean_ctor_get_uint8(v_a_693_, 0);
lean_dec(v_a_693_);
if (v_verbose_694_ == 0)
{
lean_dec_ref_known(v___x_691_, 2);
goto v___jp_670_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Meta_Sym_reportIssue(v___x_691_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_dec_ref_known(v___x_695_, 1);
goto v___jp_670_;
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___x_669_);
lean_del_object(v___x_650_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref_known(v___x_691_, 2);
lean_dec_ref(v___x_669_);
lean_del_object(v___x_650_);
v_a_704_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_692_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_692_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
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
lean_object* v___x_712_; 
lean_del_object(v___x_650_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_655_);
lean_ctor_set(v___x_712_, 1, v___x_669_);
v_a_642_ = v___x_712_;
goto v___jp_641_;
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v___x_669_);
lean_del_object(v___x_650_);
lean_dec_ref(v_e_625_);
lean_dec(v___x_624_);
v_a_713_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_682_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_682_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v___x_669_);
lean_del_object(v___x_650_);
lean_dec_ref(v_e_625_);
lean_dec(v___x_624_);
v_a_721_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_680_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_680_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
v___jp_729_:
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_655_);
lean_ctor_set(v___x_730_, 1, v___x_669_);
v_a_642_ = v___x_730_;
goto v___jp_641_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref(v___x_669_);
lean_dec(v___x_665_);
lean_del_object(v___x_650_);
lean_dec_ref(v_e_625_);
lean_dec(v___x_624_);
v_a_734_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_677_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_677_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
v___jp_670_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0));
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_669_);
lean_ctor_set(v___x_650_, 0, v___x_671_);
v___x_673_ = v___x_650_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_669_);
v___x_673_ = v_reuseFailAlloc_675_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
}
}
}
}
v___jp_641_:
{
size_t v___x_643_; size_t v___x_644_; 
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_628_, v___x_643_);
v_i_628_ = v___x_644_;
v_b_629_ = v_a_642_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_624_ = stack[0].m_obj;
lean_object* v_e_625_ = stack[1].m_obj;
lean_object* v_as_626_ = stack[2].m_obj;
size_t v_sz_627_ = stack[3].m_num;
size_t v_i_628_ = stack[4].m_num;
lean_object* v_b_629_ = stack[5].m_obj;
lean_object* v___y_630_ = stack[6].m_obj;
lean_object* v___y_631_ = stack[7].m_obj;
lean_object* v___y_632_ = stack[8].m_obj;
lean_object* v___y_633_ = stack[9].m_obj;
lean_object* v___y_634_ = stack[10].m_obj;
lean_object* v___y_635_ = stack[11].m_obj;
lean_object* v___y_636_ = stack[12].m_obj;
lean_object* v___y_637_ = stack[13].m_obj;
lean_object* v___y_638_ = stack[14].m_obj;
lean_object* v___y_639_ = stack[15].m_obj;
lean_object* v_res_749_;
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_624_, v_e_625_, v_as_626_, v_sz_627_, v_i_628_, v_b_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
stack->m_obj
 = v_res_749_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object** _args){
lean_object* v___x_750_ = _args[0];
lean_object* v_e_751_ = _args[1];
lean_object* v_as_752_ = _args[2];
lean_object* v_sz_753_ = _args[3];
lean_object* v_i_754_ = _args[4];
lean_object* v_b_755_ = _args[5];
lean_object* v___y_756_ = _args[6];
lean_object* v___y_757_ = _args[7];
lean_object* v___y_758_ = _args[8];
lean_object* v___y_759_ = _args[9];
lean_object* v___y_760_ = _args[10];
lean_object* v___y_761_ = _args[11];
lean_object* v___y_762_ = _args[12];
lean_object* v___y_763_ = _args[13];
lean_object* v___y_764_ = _args[14];
lean_object* v___y_765_ = _args[15];
lean_object* v___y_766_ = _args[16];
_start:
{
size_t v_sz_boxed_767_; size_t v_i_boxed_768_; lean_object* v_res_769_; 
v_sz_boxed_767_ = lean_unbox_usize(v_sz_753_);
lean_dec(v_sz_753_);
v_i_boxed_768_ = lean_unbox_usize(v_i_754_);
lean_dec(v_i_754_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_750_, v_e_751_, v_as_752_, v_sz_boxed_767_, v_i_boxed_768_, v_b_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v_as_752_);
return v_res_769_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10));
v___x_791_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12));
v___x_792_ = l_Lean_Name_append(v___x_791_, v___x_790_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18));
v___x_804_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17));
v___x_805_ = l_Lean_mkConst(v___x_804_, v___x_803_);
return v___x_805_;
}
}
lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object* v_e_808_, lean_object* v_thm_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_808_, v___y_810_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_812_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_1143_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_1143_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_1143_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
uint8_t v___x_840_; 
v___x_840_ = lean_nat_dec_lt(v_a_834_, v_a_836_);
lean_dec(v_a_836_);
lean_dec(v_a_834_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_dec_ref(v_thm_809_);
lean_dec_ref(v_e_808_);
v___x_841_ = lean_box(0);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_841_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
lean_object* v___x_845_; uint8_t v___x_846_; 
lean_del_object(v___x_838_);
lean_inc_ref(v_e_808_);
v___x_845_ = l_Lean_Expr_cleanupAnnotations(v_e_808_);
v___x_846_ = l_Lean_Expr_isApp(v___x_845_);
if (v___x_846_ == 0)
{
lean_dec_ref(v___x_845_);
lean_dec_ref(v_thm_809_);
lean_dec_ref(v_e_808_);
goto v___jp_830_;
}
else
{
lean_object* v_arg_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_arg_847_ = lean_ctor_get(v___x_845_, 1);
lean_inc_ref(v_arg_847_);
v___x_848_ = l_Lean_Expr_appFnCleanup___redArg(v___x_845_);
v___x_849_ = l_Lean_Expr_isApp(v___x_848_);
if (v___x_849_ == 0)
{
lean_dec_ref(v___x_848_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_thm_809_);
lean_dec_ref(v_e_808_);
goto v___jp_830_;
}
else
{
lean_object* v_arg_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_arg_850_ = lean_ctor_get(v___x_848_, 1);
lean_inc_ref(v_arg_850_);
v___x_851_ = l_Lean_Expr_appFnCleanup___redArg(v___x_848_);
v___x_852_ = l_Lean_Expr_isApp(v___x_851_);
if (v___x_852_ == 0)
{
lean_dec_ref(v___x_851_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_thm_809_);
lean_dec_ref(v_e_808_);
goto v___jp_830_;
}
else
{
lean_object* v_arg_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_arg_853_ = lean_ctor_get(v___x_851_, 1);
lean_inc_ref(v_arg_853_);
v___x_854_ = l_Lean_Expr_appFnCleanup___redArg(v___x_851_);
v___x_855_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1));
v___x_856_ = l_Lean_Expr_isConstOf(v___x_854_, v___x_855_);
lean_dec_ref(v___x_854_);
if (v___x_856_ == 0)
{
lean_dec_ref(v_arg_853_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_thm_809_);
lean_dec_ref(v_e_808_);
goto v___jp_830_;
}
else
{
lean_object* v_declName_857_; lean_object* v___y_859_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_934_; lean_object* v_a_935_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___x_987_; 
v_declName_857_ = lean_ctor_get(v_thm_809_, 0);
lean_inc_n(v_declName_857_, 2);
lean_dec_ref(v_thm_809_);
v___x_987_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_857_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_1064_; lean_object* v___x_1104_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_n(v_a_988_, 2);
lean_dec_ref_known(v___x_987_, 1);
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
v___x_1104_ = lean_infer_type(v_a_988_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; uint8_t v_transparency_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; uint8_t v___x_1110_; uint8_t v___x_1111_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = l_Lean_Meta_Context_config(v___y_816_);
v_transparency_1107_ = lean_ctor_get_uint8(v___x_1106_, 9);
lean_dec_ref(v___x_1106_);
v___x_1108_ = lean_box(0);
v___x_1109_ = 0;
v___x_1110_ = 1;
v___x_1111_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1107_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v_keyedConfig_1112_; uint8_t v_trackZetaDelta_1113_; lean_object* v_zetaDeltaSet_1114_; lean_object* v_lctx_1115_; lean_object* v_localInstances_1116_; lean_object* v_defEqCtx_x3f_1117_; lean_object* v_synthPendingDepth_1118_; lean_object* v_customCanUnfoldPredicate_x3f_1119_; uint8_t v_univApprox_1120_; uint8_t v_inTypeClassResolution_1121_; uint8_t v_cacheInferType_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_keyedConfig_1112_ = lean_ctor_get(v___y_816_, 0);
v_trackZetaDelta_1113_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*7);
v_zetaDeltaSet_1114_ = lean_ctor_get(v___y_816_, 1);
v_lctx_1115_ = lean_ctor_get(v___y_816_, 2);
v_localInstances_1116_ = lean_ctor_get(v___y_816_, 3);
v_defEqCtx_x3f_1117_ = lean_ctor_get(v___y_816_, 4);
v_synthPendingDepth_1118_ = lean_ctor_get(v___y_816_, 5);
v_customCanUnfoldPredicate_x3f_1119_ = lean_ctor_get(v___y_816_, 6);
v_univApprox_1120_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1121_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*7 + 2);
v_cacheInferType_1122_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1112_);
v___x_1123_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1110_, v_keyedConfig_1112_);
lean_inc(v_customCanUnfoldPredicate_x3f_1119_);
lean_inc(v_synthPendingDepth_1118_);
lean_inc(v_defEqCtx_x3f_1117_);
lean_inc_ref(v_localInstances_1116_);
lean_inc_ref(v_lctx_1115_);
lean_inc(v_zetaDeltaSet_1114_);
v___x_1124_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_zetaDeltaSet_1114_);
lean_ctor_set(v___x_1124_, 2, v_lctx_1115_);
lean_ctor_set(v___x_1124_, 3, v_localInstances_1116_);
lean_ctor_set(v___x_1124_, 4, v_defEqCtx_x3f_1117_);
lean_ctor_set(v___x_1124_, 5, v_synthPendingDepth_1118_);
lean_ctor_set(v___x_1124_, 6, v_customCanUnfoldPredicate_x3f_1119_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*7, v_trackZetaDelta_1113_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*7 + 1, v_univApprox_1120_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1121_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*7 + 3, v_cacheInferType_1122_);
v___x_1125_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1105_, v___x_1108_, v___x_1109_, v___x_1124_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref_known(v___x_1124_, 7);
v___y_1064_ = v___x_1125_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1105_, v___x_1108_, v___x_1109_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
v___y_1064_ = v___x_1126_;
goto v___jp_1063_;
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_arg_853_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_e_808_);
v_a_1127_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1104_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1104_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
v___jp_989_:
{
if (lean_obj_tag(v___y_993_) == 0)
{
lean_object* v_a_994_; uint8_t v___x_995_; 
v_a_994_ = lean_ctor_get(v___y_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___y_993_, 1);
v___x_995_ = lean_unbox(v_a_994_);
lean_dec(v_a_994_);
if (v___x_995_ == 0)
{
lean_dec_ref(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v_a_988_);
v___y_859_ = v___y_990_;
goto v___jp_858_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; size_t v_sz_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v___y_990_);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = lean_array_get_size(v___y_991_);
v___x_998_ = l_Array_toSubarray___redArg(v___y_991_, v___x_996_, v___x_997_);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
v_sz_1001_ = lean_array_size(v___y_992_);
v___x_1002_ = ((size_t)0ULL);
lean_inc_ref(v_e_808_);
lean_inc(v_declName_857_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_857_, v_e_808_, v___y_992_, v_sz_1001_, v___x_1002_, v___x_1000_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
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
v___x_1009_ = l_Lean_mkAppN(v_a_988_, v___y_992_);
v___x_1010_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_1009_, v___y_817_);
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
lean_inc_ref(v_e_808_);
v___x_1012_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_808_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_814_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19);
lean_inc_ref(v_e_808_);
v___x_1017_ = l_Lean_mkApp4(v___x_1016_, v_e_808_, v_a_1015_, v_a_1013_, v_a_1011_);
v___x_1018_ = lean_array_get_size(v___y_992_);
v___x_1019_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20));
v___x_1020_ = lean_nat_dec_lt(v___x_996_, v___x_1018_);
if (v___x_1020_ == 0)
{
lean_dec_ref(v___y_992_);
v___y_934_ = v___x_1017_;
v_a_935_ = v___x_1019_;
goto v___jp_933_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1018_, v___x_1018_);
if (v___x_1021_ == 0)
{
if (v___x_1020_ == 0)
{
lean_dec_ref(v___y_992_);
v___y_934_ = v___x_1017_;
v_a_935_ = v___x_1019_;
goto v___jp_933_;
}
else
{
size_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_usize_of_nat(v___x_1018_);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_992_, v___x_1002_, v___x_1022_, v___x_1019_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v___y_992_);
v___y_976_ = v___x_1017_;
v___y_977_ = v___x_1023_;
goto v___jp_975_;
}
}
else
{
size_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_usize_of_nat(v___x_1018_);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_992_, v___x_1002_, v___x_1024_, v___x_1019_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v___y_992_);
v___y_976_ = v___x_1017_;
v___y_977_ = v___x_1025_;
goto v___jp_975_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_a_1013_);
lean_dec(v_a_1011_);
lean_dec_ref(v___y_992_);
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
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
lean_dec_ref(v___y_992_);
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
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
lean_dec_ref(v___y_992_);
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
v_val_1042_ = lean_ctor_get(v_fst_1008_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v_fst_1008_, 1);
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
lean_dec_ref(v___y_992_);
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
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
lean_dec_ref(v___y_990_);
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
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
if (lean_obj_tag(v___y_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v_snd_1066_; lean_object* v_fst_1067_; lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_a_1065_ = lean_ctor_get(v___y_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___y_1064_, 1);
v_snd_1066_ = lean_ctor_get(v_a_1065_, 1);
lean_inc(v_snd_1066_);
v_fst_1067_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_fst_1067_);
lean_dec(v_a_1065_);
v_fst_1068_ = lean_ctor_get(v_snd_1066_, 0);
lean_inc(v_fst_1068_);
v_snd_1069_ = lean_ctor_get(v_snd_1066_, 1);
lean_inc_n(v_snd_1069_, 2);
lean_dec(v_snd_1066_);
v___x_1070_ = l_Lean_Expr_cleanupAnnotations(v_snd_1069_);
v___x_1071_ = l_Lean_Expr_isApp(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v___x_1070_);
lean_dec(v_snd_1069_);
lean_dec(v_fst_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_arg_853_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_e_808_);
goto v___jp_827_;
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
lean_dec(v_snd_1069_);
lean_dec(v_fst_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_arg_853_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_e_808_);
goto v___jp_827_;
}
else
{
lean_object* v_arg_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_arg_1075_ = lean_ctor_get(v___x_1073_, 1);
lean_inc_ref(v_arg_1075_);
v___x_1076_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1073_);
v___x_1077_ = l_Lean_Expr_isApp(v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec_ref(v___x_1076_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec(v_snd_1069_);
lean_dec(v_fst_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_arg_853_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_e_808_);
goto v___jp_827_;
}
else
{
lean_object* v_arg_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_arg_1078_ = lean_ctor_get(v___x_1076_, 1);
lean_inc_ref(v_arg_1078_);
v___x_1079_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1076_);
v___x_1080_ = l_Lean_Expr_isConstOf(v___x_1079_, v___x_855_);
lean_dec_ref(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v_arg_1078_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec(v_snd_1069_);
lean_dec(v_fst_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_arg_853_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_e_808_);
goto v___jp_827_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Meta_isExprDefEq(v_arg_853_, v_arg_1078_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; uint8_t v___x_1083_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v___x_1083_ = lean_unbox(v_a_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
v___y_990_ = v_snd_1069_;
v___y_991_ = v_fst_1068_;
v___y_992_ = v_fst_1067_;
v___y_993_ = v___x_1081_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1084_; 
lean_dec_ref_known(v___x_1081_, 1);
v___x_1084_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_840_, v_arg_1075_, v_arg_850_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; uint8_t v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = lean_unbox(v_a_1085_);
lean_dec(v_a_1085_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v_arg_1072_);
lean_dec(v_fst_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_a_988_);
lean_dec_ref(v_arg_847_);
v___y_859_ = v_snd_1069_;
goto v___jp_858_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_840_, v_arg_1072_, v_arg_847_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
v___y_990_ = v_snd_1069_;
v___y_991_ = v_fst_1068_;
v___y_992_ = v_fst_1067_;
v___y_993_ = v___x_1087_;
goto v___jp_989_;
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v_arg_1072_);
lean_dec(v_snd_1069_);
lean_dec(v_fst_1068_);
lean_dec(v_fst_1067_);
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_e_808_);
v_a_1088_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1084_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
v___y_990_ = v_snd_1069_;
v___y_991_ = v_fst_1068_;
v___y_992_ = v_fst_1067_;
v___y_993_ = v___x_1081_;
goto v___jp_989_;
}
}
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_a_988_);
lean_dec(v_declName_857_);
lean_dec_ref(v_arg_853_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_e_808_);
v_a_1096_ = lean_ctor_get(v___y_1064_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___y_1064_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___y_1064_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___y_1064_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_declName_857_);
lean_dec_ref(v_arg_853_);
lean_dec_ref(v_arg_850_);
lean_dec_ref(v_arg_847_);
lean_dec_ref(v_e_808_);
v_a_1135_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_987_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_987_);
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
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_860_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3);
v___x_861_ = l_Lean_MessageData_ofName(v_declName_857_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_indentExpr(v_e_808_);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_indentExpr(v___y_859_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_814_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; uint8_t v_verbose_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v_verbose_873_ = lean_ctor_get_uint8(v_a_872_, 0);
lean_dec(v_a_872_);
if (v_verbose_873_ == 0)
{
lean_dec_ref_known(v___x_870_, 2);
goto v___jp_824_;
}
else
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Sym_reportIssue(v___x_870_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_dec_ref_known(v___x_874_, 1);
goto v___jp_824_;
}
else
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref_known(v___x_870_, 2);
v_a_875_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_871_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_871_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
v___jp_883_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_884_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3);
v___x_885_ = l_Lean_MessageData_ofName(v_declName_857_);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_indentExpr(v_e_808_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_814_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; uint8_t v_verbose_895_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v_verbose_895_ = lean_ctor_get_uint8(v_a_894_, 0);
lean_dec(v_a_894_);
if (v_verbose_895_ == 0)
{
lean_dec_ref_known(v___x_892_, 2);
goto v___jp_821_;
}
else
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Meta_Sym_reportIssue(v___x_892_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_dec_ref_known(v___x_896_, 1);
goto v___jp_821_;
}
else
{
return v___x_896_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref_known(v___x_892_, 2);
v_a_897_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_893_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_893_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
v___jp_905_:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_808_, v___y_908_);
lean_dec_ref(v_e_808_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_a_919_, v___x_920_);
lean_dec(v_a_919_);
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v_declName_857_);
v___x_923_ = lean_box(1);
v___x_924_ = l_Lean_Meta_Grind_addNewRawFact(v___y_907_, v___y_906_, v___x_921_, v___x_922_, v___x_923_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v___x_924_;
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v_declName_857_);
v_a_925_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_918_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_918_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
v___jp_933_:
{
uint8_t v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; 
v___x_936_ = 0;
v___x_937_ = 1;
v___x_938_ = l_Lean_Meta_mkLambdaFVars(v_a_935_, v___y_934_, v___x_936_, v___x_840_, v___x_936_, v___x_840_, v___x_937_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v_a_935_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_940_; lean_object* v_a_941_; lean_object* v___x_942_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v___x_940_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_939_, v___y_817_);
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc_n(v_a_941_, 2);
lean_dec_ref(v___x_940_);
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
v___x_942_ = lean_infer_type(v_a_941_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; uint8_t v___x_944_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = l_Lean_Expr_hasMVar(v_a_941_);
if (v___x_944_ == 0)
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_Expr_hasMVar(v_a_943_);
if (v___x_945_ == 0)
{
lean_object* v_toCold_946_; lean_object* v_options_947_; uint8_t v_hasTrace_948_; 
v_toCold_946_ = lean_ctor_get(v___y_818_, 0);
v_options_947_ = lean_ctor_get(v_toCold_946_, 2);
v_hasTrace_948_ = lean_ctor_get_uint8(v_options_947_, sizeof(void*)*1);
if (v_hasTrace_948_ == 0)
{
v___y_906_ = v_a_943_;
v___y_907_ = v_a_941_;
v___y_908_ = v___y_810_;
v___y_909_ = v___y_811_;
v___y_910_ = v___y_812_;
v___y_911_ = v___y_813_;
v___y_912_ = v___y_814_;
v___y_913_ = v___y_815_;
v___y_914_ = v___y_816_;
v___y_915_ = v___y_817_;
v___y_916_ = v___y_818_;
v___y_917_ = v___y_819_;
goto v___jp_905_;
}
else
{
lean_object* v_inheritedTraceOptions_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_inheritedTraceOptions_949_ = lean_ctor_get(v_toCold_946_, 11);
v___x_950_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10));
v___x_951_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13);
v___x_952_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_949_, v_options_947_, v___x_951_);
if (v___x_952_ == 0)
{
v___y_906_ = v_a_943_;
v___y_907_ = v_a_941_;
v___y_908_ = v___y_810_;
v___y_909_ = v___y_811_;
v___y_910_ = v___y_812_;
v___y_911_ = v___y_813_;
v___y_912_ = v___y_814_;
v___y_913_ = v___y_815_;
v___y_914_ = v___y_816_;
v___y_915_ = v___y_817_;
v___y_916_ = v___y_818_;
v___y_917_ = v___y_819_;
goto v___jp_905_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_inc(v_declName_857_);
v___x_953_ = l_Lean_MessageData_ofName(v_declName_857_);
v___x_954_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
lean_inc(v_a_943_);
v___x_956_ = l_Lean_MessageData_ofExpr(v_a_943_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_950_, v___x_957_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_dec_ref_known(v___x_958_, 1);
v___y_906_ = v_a_943_;
v___y_907_ = v_a_941_;
v___y_908_ = v___y_810_;
v___y_909_ = v___y_811_;
v___y_910_ = v___y_812_;
v___y_911_ = v___y_813_;
v___y_912_ = v___y_814_;
v___y_913_ = v___y_815_;
v___y_914_ = v___y_816_;
v___y_915_ = v___y_817_;
v___y_916_ = v___y_818_;
v___y_917_ = v___y_819_;
goto v___jp_905_;
}
else
{
lean_dec(v_a_943_);
lean_dec(v_a_941_);
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
return v___x_958_;
}
}
}
}
else
{
lean_dec(v_a_943_);
lean_dec(v_a_941_);
goto v___jp_883_;
}
}
else
{
lean_dec(v_a_943_);
lean_dec(v_a_941_);
goto v___jp_883_;
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec(v_a_941_);
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
v_a_959_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_942_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_942_);
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
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
v_a_967_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_938_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_938_);
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
v___jp_975_:
{
if (lean_obj_tag(v___y_977_) == 0)
{
lean_object* v_a_978_; 
v_a_978_ = lean_ctor_get(v___y_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___y_977_, 1);
v___y_934_ = v___y_976_;
v_a_935_ = v_a_978_;
goto v___jp_933_;
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec_ref(v___y_976_);
lean_dec(v_declName_857_);
lean_dec_ref(v_e_808_);
v_a_979_ = lean_ctor_get(v___y_977_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___y_977_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___y_977_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___y_977_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
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
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_a_834_);
lean_dec_ref(v_thm_809_);
lean_dec_ref(v_e_808_);
v_a_1144_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_835_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_835_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v_thm_809_);
lean_dec_ref(v_e_808_);
v_a_1152_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_833_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_833_);
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
v___jp_827_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_box(0);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
v___jp_830_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_box(0);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instantiateExtTheorem___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_808_ = stack[0].m_obj;
lean_object* v_thm_809_ = stack[1].m_obj;
lean_object* v___y_810_ = stack[2].m_obj;
lean_object* v___y_811_ = stack[3].m_obj;
lean_object* v___y_812_ = stack[4].m_obj;
lean_object* v___y_813_ = stack[5].m_obj;
lean_object* v___y_814_ = stack[6].m_obj;
lean_object* v___y_815_ = stack[7].m_obj;
lean_object* v___y_816_ = stack[8].m_obj;
lean_object* v___y_817_ = stack[9].m_obj;
lean_object* v___y_818_ = stack[10].m_obj;
lean_object* v___y_819_ = stack[11].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(v_e_808_, v_thm_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object* v_e_1161_, lean_object* v_thm_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(v_e_1161_, v_thm_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec(v___y_1163_);
return v_res_1174_;
}
}
lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object* v_thm_1175_, lean_object* v_e_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___f_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed), 13, 2);
lean_closure_set(v___f_1188_, 0, v_e_1176_);
lean_closure_set(v___f_1188_, 1, v_thm_1175_);
v___x_1189_ = 0;
v___x_1190_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v___f_1188_, v___x_1189_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1190_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instantiateExtTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_1175_ = stack[0].m_obj;
lean_object* v_e_1176_ = stack[1].m_obj;
lean_object* v_a_1177_ = stack[2].m_obj;
lean_object* v_a_1178_ = stack[3].m_obj;
lean_object* v_a_1179_ = stack[4].m_obj;
lean_object* v_a_1180_ = stack[5].m_obj;
lean_object* v_a_1181_ = stack[6].m_obj;
lean_object* v_a_1182_ = stack[7].m_obj;
lean_object* v_a_1183_ = stack[8].m_obj;
lean_object* v_a_1184_ = stack[9].m_obj;
lean_object* v_a_1185_ = stack[10].m_obj;
lean_object* v_a_1186_ = stack[11].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_thm_1175_, v_e_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
stack->m_obj
 = v_res_1191_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object* v_thm_1192_, lean_object* v_e_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_thm_1192_, v_e_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec(v_a_1194_);
return v_res_1205_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object* v_mvarId_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_1206_, v___y_1214_);
return v___x_1218_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1206_ = stack[0].m_obj;
lean_object* v___y_1207_ = stack[1].m_obj;
lean_object* v___y_1208_ = stack[2].m_obj;
lean_object* v___y_1209_ = stack[3].m_obj;
lean_object* v___y_1210_ = stack[4].m_obj;
lean_object* v___y_1211_ = stack[5].m_obj;
lean_object* v___y_1212_ = stack[6].m_obj;
lean_object* v___y_1213_ = stack[7].m_obj;
lean_object* v___y_1214_ = stack[8].m_obj;
lean_object* v___y_1215_ = stack[9].m_obj;
lean_object* v___y_1216_ = stack[10].m_obj;
lean_object* v_res_1219_;
v_res_1219_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(v_mvarId_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
stack->m_obj
 = v_res_1219_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object* v_mvarId_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(v_mvarId_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v_mvarId_1220_);
return v_res_1232_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object* v_mvarId_1233_, lean_object* v_val_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_1233_, v_val_1234_, v___y_1242_);
return v___x_1246_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1233_ = stack[0].m_obj;
lean_object* v_val_1234_ = stack[1].m_obj;
lean_object* v___y_1235_ = stack[2].m_obj;
lean_object* v___y_1236_ = stack[3].m_obj;
lean_object* v___y_1237_ = stack[4].m_obj;
lean_object* v___y_1238_ = stack[5].m_obj;
lean_object* v___y_1239_ = stack[6].m_obj;
lean_object* v___y_1240_ = stack[7].m_obj;
lean_object* v___y_1241_ = stack[8].m_obj;
lean_object* v___y_1242_ = stack[9].m_obj;
lean_object* v___y_1243_ = stack[10].m_obj;
lean_object* v___y_1244_ = stack[11].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(v_mvarId_1233_, v_val_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object* v_mvarId_1248_, lean_object* v_val_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(v_mvarId_1248_, v_val_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
return v_res_1261_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object* v_cls_1262_, lean_object* v_msg_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_1262_, v_msg_1263_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1262_ = stack[0].m_obj;
lean_object* v_msg_1263_ = stack[1].m_obj;
lean_object* v___y_1264_ = stack[2].m_obj;
lean_object* v___y_1265_ = stack[3].m_obj;
lean_object* v___y_1266_ = stack[4].m_obj;
lean_object* v___y_1267_ = stack[5].m_obj;
lean_object* v___y_1268_ = stack[6].m_obj;
lean_object* v___y_1269_ = stack[7].m_obj;
lean_object* v___y_1270_ = stack[8].m_obj;
lean_object* v___y_1271_ = stack[9].m_obj;
lean_object* v___y_1272_ = stack[10].m_obj;
lean_object* v___y_1273_ = stack[11].m_obj;
lean_object* v_res_1276_;
v_res_1276_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(v_cls_1262_, v_msg_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
stack->m_obj
 = v_res_1276_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object* v_cls_1277_, lean_object* v_msg_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(v_cls_1277_, v_msg_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
return v_res_1290_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_1292_, v_x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1292_ = stack[1].m_obj;
lean_object* v_x_1293_ = stack[2].m_obj;
uint8_t v_res_1295_;
v_res_1295_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_box(0), v_x_1292_, v_x_1293_);
stack->m_num = v_res_1295_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(v_00_u03b2_1296_, v_x_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec_ref(v_x_1297_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object* v_00_u03b2_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1302_, v_x_1303_, v_x_1304_);
return v___x_1305_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1306_, lean_object* v_x_1307_, size_t v_x_1308_, lean_object* v_x_1309_){
_start:
{
uint8_t v___x_1310_; 
v___x_1310_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1307_, v_x_1308_, v_x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1307_ = stack[1].m_obj;
size_t v_x_1308_ = stack[2].m_num;
lean_object* v_x_1309_ = stack[3].m_obj;
uint8_t v_res_1311_;
v_res_1311_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_box(0), v_x_1307_, v_x_1308_, v_x_1309_);
stack->m_num = v_res_1311_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
size_t v_x_147727__boxed_1316_; uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_x_147727__boxed_1316_ = lean_unbox_usize(v_x_1314_);
lean_dec(v_x_1314_);
v_res_1317_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(v_00_u03b2_1312_, v_x_1313_, v_x_147727__boxed_1316_, v_x_1315_);
lean_dec(v_x_1315_);
lean_dec_ref(v_x_1313_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1319_, lean_object* v_x_1320_, size_t v_x_1321_, size_t v_x_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1320_, v_x_1321_, v_x_1322_, v_x_1323_, v_x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1320_ = stack[1].m_obj;
size_t v_x_1321_ = stack[2].m_num;
size_t v_x_1322_ = stack[3].m_num;
lean_object* v_x_1323_ = stack[4].m_obj;
lean_object* v_x_1324_ = stack[5].m_obj;
lean_object* v_res_1326_;
v_res_1326_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_box(0), v_x_1320_, v_x_1321_, v_x_1322_, v_x_1323_, v_x_1324_);
stack->m_obj
 = v_res_1326_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_){
_start:
{
size_t v_x_147745__boxed_1333_; size_t v_x_147746__boxed_1334_; lean_object* v_res_1335_; 
v_x_147745__boxed_1333_ = lean_unbox_usize(v_x_1329_);
lean_dec(v_x_1329_);
v_x_147746__boxed_1334_ = lean_unbox_usize(v_x_1330_);
lean_dec(v_x_1330_);
v_res_1335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(v_00_u03b2_1327_, v_x_1328_, v_x_147745__boxed_1333_, v_x_147746__boxed_1334_, v_x_1331_, v_x_1332_);
return v_res_1335_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03b2_1336_, lean_object* v_keys_1337_, lean_object* v_vals_1338_, lean_object* v_heq_1339_, lean_object* v_i_1340_, lean_object* v_k_1341_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_keys_1337_, v_i_1340_, v_k_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1337_ = stack[1].m_obj;
lean_object* v_vals_1338_ = stack[2].m_obj;
lean_object* v_i_1340_ = stack[4].m_obj;
lean_object* v_k_1341_ = stack[5].m_obj;
uint8_t v_res_1343_;
v_res_1343_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_box(0), v_keys_1337_, v_vals_1338_, lean_box(0), v_i_1340_, v_k_1341_);
stack->m_num = v_res_1343_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1344_, lean_object* v_keys_1345_, lean_object* v_vals_1346_, lean_object* v_heq_1347_, lean_object* v_i_1348_, lean_object* v_k_1349_){
_start:
{
uint8_t v_res_1350_; lean_object* v_r_1351_; 
v_res_1350_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(v_00_u03b2_1344_, v_keys_1345_, v_vals_1346_, v_heq_1347_, v_i_1348_, v_k_1349_);
lean_dec(v_k_1349_);
lean_dec_ref(v_vals_1346_);
lean_dec_ref(v_keys_1345_);
v_r_1351_ = lean_box(v_res_1350_);
return v_r_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1352_, lean_object* v_n_1353_, lean_object* v_k_1354_, lean_object* v_v_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12___redArg(v_n_1353_, v_k_1354_, v_v_1355_);
return v___x_1356_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_1357_, size_t v_depth_1358_, lean_object* v_keys_1359_, lean_object* v_vals_1360_, lean_object* v_heq_1361_, lean_object* v_i_1362_, lean_object* v_entries_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_depth_1358_, v_keys_1359_, v_vals_1360_, v_i_1362_, v_entries_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1358_ = stack[1].m_num;
lean_object* v_keys_1359_ = stack[2].m_obj;
lean_object* v_vals_1360_ = stack[3].m_obj;
lean_object* v_i_1362_ = stack[5].m_obj;
lean_object* v_entries_1363_ = stack[6].m_obj;
lean_object* v_res_1365_;
v_res_1365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_box(0), v_depth_1358_, v_keys_1359_, v_vals_1360_, lean_box(0), v_i_1362_, v_entries_1363_);
stack->m_obj
 = v_res_1365_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(lean_object* v_00_u03b2_1366_, lean_object* v_depth_1367_, lean_object* v_keys_1368_, lean_object* v_vals_1369_, lean_object* v_heq_1370_, lean_object* v_i_1371_, lean_object* v_entries_1372_){
_start:
{
size_t v_depth_boxed_1373_; lean_object* v_res_1374_; 
v_depth_boxed_1373_ = lean_unbox_usize(v_depth_1367_);
lean_dec(v_depth_1367_);
v_res_1374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(v_00_u03b2_1366_, v_depth_boxed_1373_, v_keys_1368_, v_vals_1369_, v_heq_1370_, v_i_1371_, v_entries_1372_);
lean_dec_ref(v_vals_1369_);
lean_dec_ref(v_keys_1368_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12_spec__13(lean_object* v_00_u03b2_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__12_spec__13___redArg(v_x_1376_, v_x_1377_, v_x_1378_, v_x_1379_);
return v___x_1380_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
