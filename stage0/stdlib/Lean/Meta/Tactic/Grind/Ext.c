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
size_t lean_usize_sub(size_t, size_t);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0;
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(lean_object* v_x_187_, size_t v_x_188_, size_t v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v_es_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v_j_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_es_192_ = lean_ctor_get(v_x_187_, 0);
v___x_193_ = ((size_t)31ULL);
v___x_194_ = lean_usize_land(v_x_188_, v___x_193_);
v_j_195_ = lean_usize_to_nat(v___x_194_);
v___x_196_ = lean_array_get_size(v_es_192_);
v___x_197_ = lean_nat_dec_lt(v_j_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_dec(v_j_195_);
lean_dec(v_x_191_);
lean_dec(v_x_190_);
return v_x_187_;
}
else
{
lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_236_; 
lean_inc_ref(v_es_192_);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v_x_187_, 0);
lean_dec(v_unused_237_);
v___x_199_ = v_x_187_;
v_isShared_200_ = v_isSharedCheck_236_;
goto v_resetjp_198_;
}
else
{
lean_dec(v_x_187_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_236_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_v_201_; lean_object* v___x_202_; lean_object* v_xs_x27_203_; lean_object* v___y_205_; 
v_v_201_ = lean_array_fget(v_es_192_, v_j_195_);
v___x_202_ = lean_box(0);
v_xs_x27_203_ = lean_array_fset(v_es_192_, v_j_195_, v___x_202_);
switch(lean_obj_tag(v_v_201_))
{
case 0:
{
lean_object* v_key_210_; lean_object* v_val_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_221_; 
v_key_210_ = lean_ctor_get(v_v_201_, 0);
v_val_211_ = lean_ctor_get(v_v_201_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_v_201_);
if (v_isSharedCheck_221_ == 0)
{
v___x_213_ = v_v_201_;
v_isShared_214_ = v_isSharedCheck_221_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_val_211_);
lean_inc(v_key_210_);
lean_dec(v_v_201_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_221_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_instBEqMVarId_beq(v_x_190_, v_key_210_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_del_object(v___x_213_);
v___x_216_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_210_, v_val_211_, v_x_190_, v_x_191_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
v___y_205_ = v___x_217_;
goto v___jp_204_;
}
else
{
lean_object* v___x_219_; 
lean_dec(v_val_211_);
lean_dec(v_key_210_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v_x_191_);
lean_ctor_set(v___x_213_, 0, v_x_190_);
v___x_219_ = v___x_213_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_x_190_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_x_191_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
v___y_205_ = v___x_219_;
goto v___jp_204_;
}
}
}
}
case 1:
{
lean_object* v_node_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_234_; 
v_node_222_ = lean_ctor_get(v_v_201_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_v_201_);
if (v_isSharedCheck_234_ == 0)
{
v___x_224_ = v_v_201_;
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_node_222_);
lean_dec(v_v_201_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
size_t v___x_226_; size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_226_ = ((size_t)5ULL);
v___x_227_ = lean_usize_shift_right(v_x_188_, v___x_226_);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_x_189_, v___x_228_);
v___x_230_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_node_222_, v___x_227_, v___x_229_, v_x_190_, v_x_191_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_230_);
v___x_232_ = v___x_224_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
v___y_205_ = v___x_232_;
goto v___jp_204_;
}
}
}
default: 
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_x_190_);
lean_ctor_set(v___x_235_, 1, v_x_191_);
v___y_205_ = v___x_235_;
goto v___jp_204_;
}
}
v___jp_204_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_array_fset(v_xs_x27_203_, v_j_195_, v___y_205_);
lean_dec(v_j_195_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_206_);
v___x_208_ = v___x_199_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
else
{
lean_object* v_ks_238_; lean_object* v_vs_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_259_; 
v_ks_238_ = lean_ctor_get(v_x_187_, 0);
v_vs_239_ = lean_ctor_get(v_x_187_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_259_ == 0)
{
v___x_241_ = v_x_187_;
v_isShared_242_ = v_isSharedCheck_259_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_vs_239_);
lean_inc(v_ks_238_);
lean_dec(v_x_187_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_259_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_ks_238_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_vs_239_);
v___x_244_ = v_reuseFailAlloc_258_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v_newNode_245_; uint8_t v___y_247_; size_t v___x_253_; uint8_t v___x_254_; 
v_newNode_245_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v___x_244_, v_x_190_, v_x_191_);
v___x_253_ = ((size_t)7ULL);
v___x_254_ = lean_usize_dec_le(v___x_253_, v_x_189_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_245_);
v___x_256_ = lean_unsigned_to_nat(4u);
v___x_257_ = lean_nat_dec_lt(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
v___y_247_ = v___x_257_;
goto v___jp_246_;
}
else
{
v___y_247_ = v___x_254_;
goto v___jp_246_;
}
v___jp_246_:
{
if (v___y_247_ == 0)
{
lean_object* v_ks_248_; lean_object* v_vs_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_ks_248_ = lean_ctor_get(v_newNode_245_, 0);
lean_inc_ref(v_ks_248_);
v_vs_249_ = lean_ctor_get(v_newNode_245_, 1);
lean_inc_ref(v_vs_249_);
lean_dec_ref(v_newNode_245_);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_252_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_x_189_, v_ks_248_, v_vs_249_, v___x_250_, v___x_251_);
lean_dec_ref(v_vs_249_);
lean_dec_ref(v_ks_248_);
return v___x_252_;
}
else
{
return v_newNode_245_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(size_t v_depth_260_, lean_object* v_keys_261_, lean_object* v_vals_262_, lean_object* v_i_263_, lean_object* v_entries_264_){
_start:
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = lean_array_get_size(v_keys_261_);
v___x_266_ = lean_nat_dec_lt(v_i_263_, v___x_265_);
if (v___x_266_ == 0)
{
lean_dec(v_i_263_);
return v_entries_264_;
}
else
{
lean_object* v_k_267_; lean_object* v_v_268_; uint64_t v___x_269_; size_t v_h_270_; size_t v___x_271_; lean_object* v___x_272_; size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v_h_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_k_267_ = lean_array_fget_borrowed(v_keys_261_, v_i_263_);
v_v_268_ = lean_array_fget_borrowed(v_vals_262_, v_i_263_);
v___x_269_ = l_Lean_instHashableMVarId_hash(v_k_267_);
v_h_270_ = lean_uint64_to_usize(v___x_269_);
v___x_271_ = ((size_t)5ULL);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_sub(v_depth_260_, v___x_273_);
v___x_275_ = lean_usize_mul(v___x_271_, v___x_274_);
v_h_276_ = lean_usize_shift_right(v_h_270_, v___x_275_);
v___x_277_ = lean_nat_add(v_i_263_, v___x_272_);
lean_dec(v_i_263_);
lean_inc(v_v_268_);
lean_inc(v_k_267_);
v___x_278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_entries_264_, v_h_276_, v_depth_260_, v_k_267_, v_v_268_);
v_i_263_ = v___x_277_;
v_entries_264_ = v___x_278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_depth_280_, lean_object* v_keys_281_, lean_object* v_vals_282_, lean_object* v_i_283_, lean_object* v_entries_284_){
_start:
{
size_t v_depth_boxed_285_; lean_object* v_res_286_; 
v_depth_boxed_285_ = lean_unbox_usize(v_depth_280_);
lean_dec(v_depth_280_);
v_res_286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_boxed_285_, v_keys_281_, v_vals_282_, v_i_283_, v_entries_284_);
lean_dec_ref(v_vals_282_);
lean_dec_ref(v_keys_281_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
size_t v_x_215221__boxed_292_; size_t v_x_215222__boxed_293_; lean_object* v_res_294_; 
v_x_215221__boxed_292_ = lean_unbox_usize(v_x_288_);
lean_dec(v_x_288_);
v_x_215222__boxed_293_ = lean_unbox_usize(v_x_289_);
lean_dec(v_x_289_);
v_res_294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_287_, v_x_215221__boxed_292_, v_x_215222__boxed_293_, v_x_290_, v_x_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
uint64_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
v___x_298_ = l_Lean_instHashableMVarId_hash(v_x_296_);
v___x_299_ = lean_uint64_to_usize(v___x_298_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_295_, v___x_299_, v___x_300_, v_x_296_, v_x_297_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object* v_mvarId_302_, lean_object* v_val_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_mctx_307_; lean_object* v_cache_308_; lean_object* v_zetaDeltaFVarIds_309_; lean_object* v_postponed_310_; lean_object* v_diag_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_339_; 
v___x_306_ = lean_st_ref_take(v___y_304_);
v_mctx_307_ = lean_ctor_get(v___x_306_, 0);
v_cache_308_ = lean_ctor_get(v___x_306_, 1);
v_zetaDeltaFVarIds_309_ = lean_ctor_get(v___x_306_, 2);
v_postponed_310_ = lean_ctor_get(v___x_306_, 3);
v_diag_311_ = lean_ctor_get(v___x_306_, 4);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_339_ == 0)
{
v___x_313_ = v___x_306_;
v_isShared_314_ = v_isSharedCheck_339_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_diag_311_);
lean_inc(v_postponed_310_);
lean_inc(v_zetaDeltaFVarIds_309_);
lean_inc(v_cache_308_);
lean_inc(v_mctx_307_);
lean_dec(v___x_306_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_339_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_depth_315_; lean_object* v_levelAssignDepth_316_; lean_object* v_lmvarCounter_317_; lean_object* v_mvarCounter_318_; lean_object* v_lDecls_319_; lean_object* v_decls_320_; lean_object* v_userNames_321_; lean_object* v_lAssignment_322_; lean_object* v_eAssignment_323_; lean_object* v_dAssignment_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_338_; 
v_depth_315_ = lean_ctor_get(v_mctx_307_, 0);
v_levelAssignDepth_316_ = lean_ctor_get(v_mctx_307_, 1);
v_lmvarCounter_317_ = lean_ctor_get(v_mctx_307_, 2);
v_mvarCounter_318_ = lean_ctor_get(v_mctx_307_, 3);
v_lDecls_319_ = lean_ctor_get(v_mctx_307_, 4);
v_decls_320_ = lean_ctor_get(v_mctx_307_, 5);
v_userNames_321_ = lean_ctor_get(v_mctx_307_, 6);
v_lAssignment_322_ = lean_ctor_get(v_mctx_307_, 7);
v_eAssignment_323_ = lean_ctor_get(v_mctx_307_, 8);
v_dAssignment_324_ = lean_ctor_get(v_mctx_307_, 9);
v_isSharedCheck_338_ = !lean_is_exclusive(v_mctx_307_);
if (v_isSharedCheck_338_ == 0)
{
v___x_326_ = v_mctx_307_;
v_isShared_327_ = v_isSharedCheck_338_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_dAssignment_324_);
lean_inc(v_eAssignment_323_);
lean_inc(v_lAssignment_322_);
lean_inc(v_userNames_321_);
lean_inc(v_decls_320_);
lean_inc(v_lDecls_319_);
lean_inc(v_mvarCounter_318_);
lean_inc(v_lmvarCounter_317_);
lean_inc(v_levelAssignDepth_316_);
lean_inc(v_depth_315_);
lean_dec(v_mctx_307_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_338_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_eAssignment_323_, v_mvarId_302_, v_val_303_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 8, v___x_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_depth_315_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_levelAssignDepth_316_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_lmvarCounter_317_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_mvarCounter_318_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_lDecls_319_);
lean_ctor_set(v_reuseFailAlloc_337_, 5, v_decls_320_);
lean_ctor_set(v_reuseFailAlloc_337_, 6, v_userNames_321_);
lean_ctor_set(v_reuseFailAlloc_337_, 7, v_lAssignment_322_);
lean_ctor_set(v_reuseFailAlloc_337_, 8, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_337_, 9, v_dAssignment_324_);
v___x_330_ = v_reuseFailAlloc_337_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_330_);
v___x_332_ = v___x_313_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_cache_308_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_zetaDeltaFVarIds_309_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_postponed_310_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v_diag_311_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_st_ref_set(v___y_304_, v___x_332_);
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object* v_mvarId_340_, lean_object* v_val_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_340_, v_val_341_, v___y_342_);
lean_dec(v___y_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(uint8_t v___x_345_, lean_object* v_p_346_, lean_object* v_e_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = l_Lean_Expr_isMVar(v_p_346_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_isExprDefEq(v_p_346_, v_e_347_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v___x_361_ = l_Lean_Expr_mvarId_x21(v_p_346_);
lean_dec_ref(v_p_346_);
v___x_362_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_361_, v_e_347_, v___y_355_);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_371_);
v___x_364_ = v___x_362_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_dec(v___x_362_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_box(v___x_345_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object* v___x_372_, lean_object* v_p_373_, lean_object* v_e_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
uint8_t v___x_215434__boxed_386_; lean_object* v_res_387_; 
v___x_215434__boxed_386_ = lean_unbox(v___x_372_);
v_res_387_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_215434__boxed_386_, v_p_373_, v_e_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec(v___y_375_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(lean_object* v_msgData_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v_env_395_; lean_object* v___x_396_; lean_object* v_mctx_397_; lean_object* v_lctx_398_; lean_object* v_options_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_394_ = lean_st_ref_get(v___y_392_);
v_env_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_env_395_);
lean_dec(v___x_394_);
v___x_396_ = lean_st_ref_get(v___y_390_);
v_mctx_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_mctx_397_);
lean_dec(v___x_396_);
v_lctx_398_ = lean_ctor_get(v___y_389_, 2);
v_options_399_ = lean_ctor_get(v___y_391_, 2);
lean_inc_ref(v_options_399_);
lean_inc_ref(v_lctx_398_);
v___x_400_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_400_, 0, v_env_395_);
lean_ctor_set(v___x_400_, 1, v_mctx_397_);
lean_ctor_set(v___x_400_, 2, v_lctx_398_);
lean_ctor_set(v___x_400_, 3, v_options_399_);
v___x_401_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v_msgData_388_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6___boxed(lean_object* v_msgData_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msgData_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_410_; double v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_float_of_nat(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object* v_cls_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_ref_422_; lean_object* v___x_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_468_; 
v_ref_422_ = lean_ctor_get(v___y_419_, 5);
v___x_423_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_468_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_468_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_468_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v_traceState_429_; lean_object* v_env_430_; lean_object* v_nextMacroScope_431_; lean_object* v_ngen_432_; lean_object* v_auxDeclNGen_433_; lean_object* v_cache_434_; lean_object* v_messages_435_; lean_object* v_infoState_436_; lean_object* v_snapshotTasks_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_467_; 
v___x_428_ = lean_st_ref_take(v___y_420_);
v_traceState_429_ = lean_ctor_get(v___x_428_, 4);
v_env_430_ = lean_ctor_get(v___x_428_, 0);
v_nextMacroScope_431_ = lean_ctor_get(v___x_428_, 1);
v_ngen_432_ = lean_ctor_get(v___x_428_, 2);
v_auxDeclNGen_433_ = lean_ctor_get(v___x_428_, 3);
v_cache_434_ = lean_ctor_get(v___x_428_, 5);
v_messages_435_ = lean_ctor_get(v___x_428_, 6);
v_infoState_436_ = lean_ctor_get(v___x_428_, 7);
v_snapshotTasks_437_ = lean_ctor_get(v___x_428_, 8);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_467_ == 0)
{
v___x_439_ = v___x_428_;
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snapshotTasks_437_);
lean_inc(v_infoState_436_);
lean_inc(v_messages_435_);
lean_inc(v_cache_434_);
lean_inc(v_traceState_429_);
lean_inc(v_auxDeclNGen_433_);
lean_inc(v_ngen_432_);
lean_inc(v_nextMacroScope_431_);
lean_inc(v_env_430_);
lean_dec(v___x_428_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint64_t v_tid_441_; lean_object* v_traces_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_466_; 
v_tid_441_ = lean_ctor_get_uint64(v_traceState_429_, sizeof(void*)*1);
v_traces_442_ = lean_ctor_get(v_traceState_429_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_traceState_429_);
if (v_isSharedCheck_466_ == 0)
{
v___x_444_ = v_traceState_429_;
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_traces_442_);
lean_dec(v_traceState_429_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; double v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_446_ = lean_box(0);
v___x_447_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0);
v___x_448_ = 0;
v___x_449_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
v___x_450_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_450_, 0, v_cls_415_);
lean_ctor_set(v___x_450_, 1, v___x_446_);
lean_ctor_set(v___x_450_, 2, v___x_449_);
lean_ctor_set_float(v___x_450_, sizeof(void*)*3, v___x_447_);
lean_ctor_set_float(v___x_450_, sizeof(void*)*3 + 8, v___x_447_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*3 + 16, v___x_448_);
v___x_451_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2));
v___x_452_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v_a_424_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
lean_inc(v_ref_422_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_ref_422_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Lean_PersistentArray_push___redArg(v_traces_442_, v___x_453_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_454_);
v___x_456_ = v___x_444_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_454_);
lean_ctor_set_uint64(v_reuseFailAlloc_465_, sizeof(void*)*1, v_tid_441_);
v___x_456_ = v_reuseFailAlloc_465_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 4, v___x_456_);
v___x_458_ = v___x_439_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_env_430_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_nextMacroScope_431_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_ngen_432_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_auxDeclNGen_433_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_cache_434_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_messages_435_);
lean_ctor_set(v_reuseFailAlloc_464_, 7, v_infoState_436_);
lean_ctor_set(v_reuseFailAlloc_464_, 8, v_snapshotTasks_437_);
v___x_458_ = v_reuseFailAlloc_464_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = lean_st_ref_set(v___y_420_, v___x_458_);
v___x_460_ = lean_box(0);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_460_);
v___x_462_ = v___x_426_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object* v_cls_469_, lean_object* v_msg_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_469_, v_msg_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_keys_477_, lean_object* v_i_478_, lean_object* v_k_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_array_get_size(v_keys_477_);
v___x_481_ = lean_nat_dec_lt(v_i_478_, v___x_480_);
if (v___x_481_ == 0)
{
lean_dec(v_i_478_);
return v___x_481_;
}
else
{
lean_object* v_k_x27_482_; uint8_t v___x_483_; 
v_k_x27_482_ = lean_array_fget_borrowed(v_keys_477_, v_i_478_);
v___x_483_ = l_Lean_instBEqMVarId_beq(v_k_479_, v_k_x27_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_i_478_, v___x_484_);
lean_dec(v_i_478_);
v_i_478_ = v___x_485_;
goto _start;
}
else
{
lean_dec(v_i_478_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_keys_487_, lean_object* v_i_488_, lean_object* v_k_489_){
_start:
{
uint8_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_487_, v_i_488_, v_k_489_);
lean_dec(v_k_489_);
lean_dec_ref(v_keys_487_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(lean_object* v_x_492_, size_t v_x_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
lean_object* v_es_495_; lean_object* v___x_496_; size_t v___x_497_; size_t v___x_498_; lean_object* v_j_499_; lean_object* v___x_500_; 
v_es_495_ = lean_ctor_get(v_x_492_, 0);
v___x_496_ = lean_box(2);
v___x_497_ = ((size_t)31ULL);
v___x_498_ = lean_usize_land(v_x_493_, v___x_497_);
v_j_499_ = lean_usize_to_nat(v___x_498_);
v___x_500_ = lean_array_get_borrowed(v___x_496_, v_es_495_, v_j_499_);
lean_dec(v_j_499_);
switch(lean_obj_tag(v___x_500_))
{
case 0:
{
lean_object* v_key_501_; uint8_t v___x_502_; 
v_key_501_ = lean_ctor_get(v___x_500_, 0);
v___x_502_ = l_Lean_instBEqMVarId_beq(v_x_494_, v_key_501_);
return v___x_502_;
}
case 1:
{
lean_object* v_node_503_; size_t v___x_504_; size_t v___x_505_; 
v_node_503_ = lean_ctor_get(v___x_500_, 0);
v___x_504_ = ((size_t)5ULL);
v___x_505_ = lean_usize_shift_right(v_x_493_, v___x_504_);
v_x_492_ = v_node_503_;
v_x_493_ = v___x_505_;
goto _start;
}
default: 
{
uint8_t v___x_507_; 
v___x_507_ = 0;
return v___x_507_;
}
}
}
else
{
lean_object* v_ks_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_ks_508_ = lean_ctor_get(v_x_492_, 0);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_ks_508_, v___x_509_, v_x_494_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
size_t v_x_215637__boxed_514_; uint8_t v_res_515_; lean_object* v_r_516_; 
v_x_215637__boxed_514_ = lean_unbox_usize(v_x_512_);
lean_dec(v_x_512_);
v_res_515_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_511_, v_x_215637__boxed_514_, v_x_513_);
lean_dec(v_x_513_);
lean_dec_ref(v_x_511_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
uint64_t v___x_519_; size_t v___x_520_; uint8_t v___x_521_; 
v___x_519_ = l_Lean_instHashableMVarId_hash(v_x_518_);
v___x_520_ = lean_uint64_to_usize(v___x_519_);
v___x_521_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_517_, v___x_520_, v_x_518_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_522_, v_x_523_);
lean_dec(v_x_523_);
lean_dec_ref(v_x_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object* v_mvarId_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v_mctx_530_; lean_object* v_eAssignment_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_529_ = lean_st_ref_get(v___y_527_);
v_mctx_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_mctx_530_);
lean_dec(v___x_529_);
v_eAssignment_531_ = lean_ctor_get(v_mctx_530_, 8);
lean_inc_ref(v_eAssignment_531_);
lean_dec_ref(v_mctx_530_);
v___x_532_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_531_, v_mvarId_526_);
lean_dec_ref(v_eAssignment_531_);
v___x_533_ = lean_box(v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object* v_mvarId_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec(v_mvarId_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object* v_as_539_, size_t v_i_540_, size_t v_stop_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_a_555_; uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_eq(v_i_540_, v_stop_541_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_560_ = lean_array_uget_borrowed(v_as_539_, v_i_540_);
v___x_563_ = l_Lean_Expr_mvarId_x21(v___x_560_);
v___x_564_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_563_, v___y_550_);
lean_dec(v___x_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; uint8_t v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v___x_566_ = lean_unbox(v_a_565_);
lean_dec(v_a_565_);
if (v___x_566_ == 0)
{
goto v___jp_561_;
}
else
{
v_a_555_ = v_b_542_;
goto v___jp_554_;
}
}
else
{
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_567_; uint8_t v___x_568_; 
v_a_567_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_564_, 1);
v___x_568_ = lean_unbox(v_a_567_);
lean_dec(v_a_567_);
if (v___x_568_ == 0)
{
v_a_555_ = v_b_542_;
goto v___jp_554_;
}
else
{
goto v___jp_561_;
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec_ref(v_b_542_);
v_a_569_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_564_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_564_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
v___jp_561_:
{
lean_object* v___x_562_; 
lean_inc(v___x_560_);
v___x_562_ = lean_array_push(v_b_542_, v___x_560_);
v_a_555_ = v___x_562_;
goto v___jp_554_;
}
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_b_542_);
return v___x_577_;
}
v___jp_554_:
{
size_t v___x_556_; size_t v___x_557_; 
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_i_540_, v___x_556_);
v_i_540_ = v___x_557_;
v_b_542_ = v_a_555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object* v_as_578_, lean_object* v_i_579_, lean_object* v_stop_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
size_t v_i_boxed_593_; size_t v_stop_boxed_594_; lean_object* v_res_595_; 
v_i_boxed_593_ = lean_unbox_usize(v_i_579_);
lean_dec(v_i_579_);
v_stop_boxed_594_ = lean_unbox_usize(v_stop_580_);
lean_dec(v_stop_580_);
v_res_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_578_, v_i_boxed_593_, v_stop_boxed_594_, v_b_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v_as_578_);
return v_res_595_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1));
v___x_600_ = l_Lean_stringToMessageData(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3));
v___x_603_ = l_Lean_stringToMessageData(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object* v___x_604_, lean_object* v_e_605_, lean_object* v_as_606_, size_t v_sz_607_, size_t v_i_608_, lean_object* v_b_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_a_622_; uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_608_, v_sz_607_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref(v_e_605_);
lean_dec(v___x_604_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_b_609_);
return v___x_627_;
}
else
{
lean_object* v_snd_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_734_; 
v_snd_628_ = lean_ctor_get(v_b_609_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_b_609_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_b_609_, 0);
lean_dec(v_unused_735_);
v___x_630_ = v_b_609_;
v_isShared_631_ = v_isSharedCheck_734_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_snd_628_);
lean_dec(v_b_609_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_734_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_array_632_; lean_object* v_start_633_; lean_object* v_stop_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_array_632_ = lean_ctor_get(v_snd_628_, 0);
v_start_633_ = lean_ctor_get(v_snd_628_, 1);
v_stop_634_ = lean_ctor_get(v_snd_628_, 2);
v___x_635_ = lean_box(0);
v___x_636_ = lean_nat_dec_lt(v_start_633_, v_stop_634_);
if (v___x_636_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref(v_e_605_);
lean_dec(v___x_604_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_635_);
v___x_638_ = v___x_630_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_snd_628_);
v___x_638_ = v_reuseFailAlloc_640_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; 
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
else
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_730_; 
lean_inc(v_stop_634_);
lean_inc(v_start_633_);
lean_inc_ref(v_array_632_);
v_isSharedCheck_730_ = !lean_is_exclusive(v_snd_628_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; lean_object* v_unused_732_; lean_object* v_unused_733_; 
v_unused_731_ = lean_ctor_get(v_snd_628_, 2);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_snd_628_, 1);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_snd_628_, 0);
lean_dec(v_unused_733_);
v___x_642_ = v_snd_628_;
v_isShared_643_ = v_isSharedCheck_730_;
goto v_resetjp_641_;
}
else
{
lean_dec(v_snd_628_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_730_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_a_644_ = lean_array_uget_borrowed(v_as_606_, v_i_608_);
v___x_645_ = l_Lean_Expr_mvarId_x21(v_a_644_);
v___x_646_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_645_, v___y_617_);
lean_dec(v___x_645_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_721_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_721_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_721_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_721_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_651_ = lean_array_fget(v_array_632_, v_start_633_);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_add(v_start_633_, v___x_652_);
lean_dec(v_start_633_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v___x_653_);
v___x_655_ = v___x_642_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_array_632_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_stop_634_);
v___x_655_ = v_reuseFailAlloc_720_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
uint8_t v___y_667_; uint8_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_unbox(v___x_651_);
lean_dec(v___x_651_);
v___x_718_ = l_Lean_BinderInfo_isInstImplicit(v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v_a_647_);
v___y_667_ = v___x_718_;
goto v___jp_666_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_unbox(v_a_647_);
lean_dec(v_a_647_);
if (v___x_719_ == 0)
{
v___y_667_ = v___x_718_;
goto v___jp_666_;
}
else
{
lean_del_object(v___x_649_);
lean_del_object(v___x_630_);
goto v___jp_664_;
}
}
v___jp_656_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0));
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_655_);
lean_ctor_set(v___x_630_, 0, v___x_657_);
v___x_659_ = v___x_630_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_655_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_659_);
v___x_661_ = v___x_649_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
v___jp_664_:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_635_);
lean_ctor_set(v___x_665_, 1, v___x_655_);
v_a_622_ = v___x_665_;
goto v___jp_621_;
}
v___jp_666_:
{
if (v___y_667_ == 0)
{
lean_del_object(v___x_649_);
lean_del_object(v___x_630_);
goto v___jp_664_;
}
else
{
lean_object* v___x_668_; 
lean_inc(v___y_619_);
lean_inc_ref(v___y_618_);
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v_a_644_);
v___x_668_ = lean_infer_type(v_a_644_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
lean_inc(v_a_644_);
v___x_670_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_a_644_, v_a_669_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_unbox(v_a_671_);
lean_dec(v_a_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_614_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; uint8_t v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = lean_unbox(v_a_674_);
lean_dec(v_a_674_);
if (v___x_675_ == 0)
{
lean_dec_ref(v_e_605_);
lean_dec(v___x_604_);
goto v___jp_656_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_676_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
v___x_677_ = l_Lean_MessageData_ofName(v___x_604_);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = l_Lean_indentExpr(v_e_605_);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Lean_Meta_Sym_reportIssue(v___x_682_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_dec_ref_known(v___x_683_, 1);
goto v___jp_656_;
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v___x_655_);
lean_del_object(v___x_649_);
lean_del_object(v___x_630_);
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v___x_655_);
lean_del_object(v___x_649_);
lean_del_object(v___x_630_);
lean_dec_ref(v_e_605_);
lean_dec(v___x_604_);
v_a_692_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_673_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_673_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_700_; 
lean_del_object(v___x_649_);
lean_del_object(v___x_630_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_635_);
lean_ctor_set(v___x_700_, 1, v___x_655_);
v_a_622_ = v___x_700_;
goto v___jp_621_;
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v___x_655_);
lean_del_object(v___x_649_);
lean_del_object(v___x_630_);
lean_dec_ref(v_e_605_);
lean_dec(v___x_604_);
v_a_701_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_670_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_670_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v___x_655_);
lean_del_object(v___x_649_);
lean_del_object(v___x_630_);
lean_dec_ref(v_e_605_);
lean_dec(v___x_604_);
v_a_709_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_668_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_668_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
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
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_del_object(v___x_642_);
lean_dec(v_stop_634_);
lean_dec(v_start_633_);
lean_dec_ref(v_array_632_);
lean_del_object(v___x_630_);
lean_dec_ref(v_e_605_);
lean_dec(v___x_604_);
v_a_722_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_646_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_646_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
}
v___jp_621_:
{
size_t v___x_623_; size_t v___x_624_; 
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_608_, v___x_623_);
v_i_608_ = v___x_624_;
v_b_609_ = v_a_622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object** _args){
lean_object* v___x_736_ = _args[0];
lean_object* v_e_737_ = _args[1];
lean_object* v_as_738_ = _args[2];
lean_object* v_sz_739_ = _args[3];
lean_object* v_i_740_ = _args[4];
lean_object* v_b_741_ = _args[5];
lean_object* v___y_742_ = _args[6];
lean_object* v___y_743_ = _args[7];
lean_object* v___y_744_ = _args[8];
lean_object* v___y_745_ = _args[9];
lean_object* v___y_746_ = _args[10];
lean_object* v___y_747_ = _args[11];
lean_object* v___y_748_ = _args[12];
lean_object* v___y_749_ = _args[13];
lean_object* v___y_750_ = _args[14];
lean_object* v___y_751_ = _args[15];
lean_object* v___y_752_ = _args[16];
_start:
{
size_t v_sz_boxed_753_; size_t v_i_boxed_754_; lean_object* v_res_755_; 
v_sz_boxed_753_ = lean_unbox_usize(v_sz_739_);
lean_dec(v_sz_739_);
v_i_boxed_754_ = lean_unbox_usize(v_i_740_);
lean_dec(v_i_740_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_736_, v_e_737_, v_as_738_, v_sz_boxed_753_, v_i_boxed_754_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v_as_738_);
return v_res_755_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_768_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6));
v___x_769_ = l_Lean_Name_append(v___x_768_, v___x_767_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18));
v___x_790_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17));
v___x_791_ = l_Lean_mkConst(v___x_790_, v___x_789_);
return v___x_791_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21(void){
_start:
{
uint8_t v___x_794_; uint64_t v___x_795_; 
v___x_794_ = 1;
v___x_795_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object* v_e_796_, lean_object* v_thm_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_796_, v___y_798_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_800_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_1164_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_1164_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_1164_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint8_t v___x_828_; 
v___x_828_ = lean_nat_dec_lt(v_a_822_, v_a_824_);
lean_dec(v_a_824_);
lean_dec(v_a_822_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_831_; 
lean_dec_ref(v_thm_797_);
lean_dec_ref(v_e_796_);
v___x_829_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_829_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
lean_object* v___x_833_; uint8_t v___x_834_; 
lean_del_object(v___x_826_);
lean_inc_ref(v_e_796_);
v___x_833_ = l_Lean_Expr_cleanupAnnotations(v_e_796_);
v___x_834_ = l_Lean_Expr_isApp(v___x_833_);
if (v___x_834_ == 0)
{
lean_dec_ref(v___x_833_);
lean_dec_ref(v_thm_797_);
lean_dec_ref(v_e_796_);
goto v___jp_818_;
}
else
{
lean_object* v_arg_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_arg_835_ = lean_ctor_get(v___x_833_, 1);
lean_inc_ref(v_arg_835_);
v___x_836_ = l_Lean_Expr_appFnCleanup___redArg(v___x_833_);
v___x_837_ = l_Lean_Expr_isApp(v___x_836_);
if (v___x_837_ == 0)
{
lean_dec_ref(v___x_836_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_thm_797_);
lean_dec_ref(v_e_796_);
goto v___jp_818_;
}
else
{
lean_object* v_arg_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_arg_838_ = lean_ctor_get(v___x_836_, 1);
lean_inc_ref(v_arg_838_);
v___x_839_ = l_Lean_Expr_appFnCleanup___redArg(v___x_836_);
v___x_840_ = l_Lean_Expr_isApp(v___x_839_);
if (v___x_840_ == 0)
{
lean_dec_ref(v___x_839_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_thm_797_);
lean_dec_ref(v_e_796_);
goto v___jp_818_;
}
else
{
lean_object* v_arg_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_arg_841_ = lean_ctor_get(v___x_839_, 1);
lean_inc_ref(v_arg_841_);
v___x_842_ = l_Lean_Expr_appFnCleanup___redArg(v___x_839_);
v___x_843_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1));
v___x_844_ = l_Lean_Expr_isConstOf(v___x_842_, v___x_843_);
lean_dec_ref(v___x_842_);
if (v___x_844_ == 0)
{
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_thm_797_);
lean_dec_ref(v_e_796_);
goto v___jp_818_;
}
else
{
lean_object* v_declName_845_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_875_; lean_object* v___y_876_; uint8_t v___y_877_; uint8_t v___y_912_; lean_object* v___y_913_; lean_object* v_a_914_; uint8_t v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_955_; lean_object* v___x_979_; 
v_declName_845_ = lean_ctor_get(v_thm_797_, 0);
lean_inc_n(v_declName_845_, 2);
lean_dec_ref(v_thm_797_);
v___x_979_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_845_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___y_982_; lean_object* v___y_983_; uint8_t v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v_a_1057_; lean_object* v___x_1088_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc_n(v_a_980_, 2);
lean_dec_ref_known(v___x_979_, 1);
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
v___x_1088_ = lean_infer_type(v_a_980_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; uint8_t v_foApprox_1091_; uint8_t v_ctxApprox_1092_; uint8_t v_quasiPatternApprox_1093_; uint8_t v_constApprox_1094_; uint8_t v_isDefEqStuckEx_1095_; uint8_t v_unificationHints_1096_; uint8_t v_proofIrrelevance_1097_; uint8_t v_assignSyntheticOpaque_1098_; uint8_t v_offsetCnstrs_1099_; uint8_t v_etaStruct_1100_; uint8_t v_univApprox_1101_; uint8_t v_iota_1102_; uint8_t v_beta_1103_; uint8_t v_proj_1104_; uint8_t v_zeta_1105_; uint8_t v_zetaDelta_1106_; uint8_t v_zetaUnused_1107_; uint8_t v_zetaHave_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1147_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l_Lean_Meta_Context_config(v___y_804_);
v_foApprox_1091_ = lean_ctor_get_uint8(v___x_1090_, 0);
v_ctxApprox_1092_ = lean_ctor_get_uint8(v___x_1090_, 1);
v_quasiPatternApprox_1093_ = lean_ctor_get_uint8(v___x_1090_, 2);
v_constApprox_1094_ = lean_ctor_get_uint8(v___x_1090_, 3);
v_isDefEqStuckEx_1095_ = lean_ctor_get_uint8(v___x_1090_, 4);
v_unificationHints_1096_ = lean_ctor_get_uint8(v___x_1090_, 5);
v_proofIrrelevance_1097_ = lean_ctor_get_uint8(v___x_1090_, 6);
v_assignSyntheticOpaque_1098_ = lean_ctor_get_uint8(v___x_1090_, 7);
v_offsetCnstrs_1099_ = lean_ctor_get_uint8(v___x_1090_, 8);
v_etaStruct_1100_ = lean_ctor_get_uint8(v___x_1090_, 10);
v_univApprox_1101_ = lean_ctor_get_uint8(v___x_1090_, 11);
v_iota_1102_ = lean_ctor_get_uint8(v___x_1090_, 12);
v_beta_1103_ = lean_ctor_get_uint8(v___x_1090_, 13);
v_proj_1104_ = lean_ctor_get_uint8(v___x_1090_, 14);
v_zeta_1105_ = lean_ctor_get_uint8(v___x_1090_, 15);
v_zetaDelta_1106_ = lean_ctor_get_uint8(v___x_1090_, 16);
v_zetaUnused_1107_ = lean_ctor_get_uint8(v___x_1090_, 17);
v_zetaHave_1108_ = lean_ctor_get_uint8(v___x_1090_, 18);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1110_ = v___x_1090_;
v_isShared_1111_ = v_isSharedCheck_1147_;
goto v_resetjp_1109_;
}
else
{
lean_dec(v___x_1090_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1147_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint8_t v_trackZetaDelta_1112_; lean_object* v_zetaDeltaSet_1113_; lean_object* v_lctx_1114_; lean_object* v_localInstances_1115_; lean_object* v_defEqCtx_x3f_1116_; lean_object* v_synthPendingDepth_1117_; lean_object* v_canUnfold_x3f_1118_; uint8_t v_univApprox_1119_; uint8_t v_inTypeClassResolution_1120_; uint8_t v_cacheInferType_1121_; uint8_t v___x_1122_; lean_object* v_config_1124_; 
v_trackZetaDelta_1112_ = lean_ctor_get_uint8(v___y_804_, sizeof(void*)*7);
v_zetaDeltaSet_1113_ = lean_ctor_get(v___y_804_, 1);
v_lctx_1114_ = lean_ctor_get(v___y_804_, 2);
v_localInstances_1115_ = lean_ctor_get(v___y_804_, 3);
v_defEqCtx_x3f_1116_ = lean_ctor_get(v___y_804_, 4);
v_synthPendingDepth_1117_ = lean_ctor_get(v___y_804_, 5);
v_canUnfold_x3f_1118_ = lean_ctor_get(v___y_804_, 6);
v_univApprox_1119_ = lean_ctor_get_uint8(v___y_804_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1120_ = lean_ctor_get_uint8(v___y_804_, sizeof(void*)*7 + 2);
v_cacheInferType_1121_ = lean_ctor_get_uint8(v___y_804_, sizeof(void*)*7 + 3);
v___x_1122_ = 1;
if (v_isShared_1111_ == 0)
{
v_config_1124_ = v___x_1110_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 0, v_foApprox_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 1, v_ctxApprox_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 2, v_quasiPatternApprox_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 3, v_constApprox_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 4, v_isDefEqStuckEx_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 5, v_unificationHints_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 6, v_proofIrrelevance_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 7, v_assignSyntheticOpaque_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 8, v_offsetCnstrs_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 10, v_etaStruct_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 11, v_univApprox_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 12, v_iota_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 13, v_beta_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 14, v_proj_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 15, v_zeta_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 16, v_zetaDelta_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 17, v_zetaUnused_1107_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, 18, v_zetaHave_1108_);
v_config_1124_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
uint64_t v___x_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; uint64_t v_key_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_ctor_set_uint8(v_config_1124_, 9, v___x_1122_);
v___x_1125_ = l_Lean_Meta_Context_configKey(v___y_804_);
v___x_1126_ = 3ULL;
v___x_1127_ = lean_uint64_shift_right(v___x_1125_, v___x_1126_);
v___x_1128_ = lean_box(0);
v___x_1129_ = 0;
v___x_1130_ = lean_uint64_shift_left(v___x_1127_, v___x_1126_);
v___x_1131_ = lean_uint64_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21);
v_key_1132_ = lean_uint64_lor(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1133_, 0, v_config_1124_);
lean_ctor_set_uint64(v___x_1133_, sizeof(void*)*1, v_key_1132_);
lean_inc(v_canUnfold_x3f_1118_);
lean_inc(v_synthPendingDepth_1117_);
lean_inc(v_defEqCtx_x3f_1116_);
lean_inc_ref(v_localInstances_1115_);
lean_inc_ref(v_lctx_1114_);
lean_inc(v_zetaDeltaSet_1113_);
v___x_1134_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_zetaDeltaSet_1113_);
lean_ctor_set(v___x_1134_, 2, v_lctx_1114_);
lean_ctor_set(v___x_1134_, 3, v_localInstances_1115_);
lean_ctor_set(v___x_1134_, 4, v_defEqCtx_x3f_1116_);
lean_ctor_set(v___x_1134_, 5, v_synthPendingDepth_1117_);
lean_ctor_set(v___x_1134_, 6, v_canUnfold_x3f_1118_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*7, v_trackZetaDelta_1112_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*7 + 1, v_univApprox_1119_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1120_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*7 + 3, v_cacheInferType_1121_);
v___x_1135_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1089_, v___x_1128_, v___x_1129_, v___x_1134_, v___y_805_, v___y_806_, v___y_807_);
lean_dec_ref_known(v___x_1134_, 7);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v_a_1057_ = v_a_1136_;
goto v___jp_1056_;
}
else
{
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1137_; 
v_a_1137_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1135_, 1);
v_a_1057_ = v_a_1137_;
goto v___jp_1056_;
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_e_796_);
v_a_1138_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1135_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1135_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_e_796_);
v_a_1148_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1088_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1088_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
v___jp_981_:
{
if (lean_obj_tag(v___y_986_) == 0)
{
lean_object* v_a_987_; uint8_t v___x_988_; 
v_a_987_ = lean_ctor_get(v___y_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___y_986_, 1);
v___x_988_ = lean_unbox(v_a_987_);
lean_dec(v_a_987_);
if (v___x_988_ == 0)
{
lean_dec_ref(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v_a_980_);
v___y_955_ = v___y_985_;
goto v___jp_954_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; size_t v_sz_994_; size_t v___x_995_; lean_object* v___x_996_; 
lean_dec_ref(v___y_985_);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_array_get_size(v___y_983_);
v___x_991_ = l_Array_toSubarray___redArg(v___y_983_, v___x_989_, v___x_990_);
v___x_992_ = lean_box(0);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_991_);
v_sz_994_ = lean_array_size(v___y_982_);
v___x_995_ = ((size_t)0ULL);
lean_inc_ref(v_e_796_);
lean_inc(v_declName_845_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_845_, v_e_796_, v___y_982_, v_sz_994_, v___x_995_, v___x_993_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1039_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1039_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1039_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_fst_1001_; 
v_fst_1001_ = lean_ctor_get(v_a_997_, 0);
lean_inc(v_fst_1001_);
lean_dec(v_a_997_);
if (lean_obj_tag(v_fst_1001_) == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_a_1004_; lean_object* v___x_1005_; 
lean_del_object(v___x_999_);
v___x_1002_ = l_Lean_mkAppN(v_a_980_, v___y_982_);
v___x_1003_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_1002_, v___y_805_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
lean_inc_ref(v_e_796_);
v___x_1005_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_796_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_802_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19);
lean_inc_ref(v_e_796_);
v___x_1010_ = l_Lean_mkApp4(v___x_1009_, v_e_796_, v_a_1008_, v_a_1006_, v_a_1004_);
v___x_1011_ = lean_array_get_size(v___y_982_);
v___x_1012_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20));
v___x_1013_ = lean_nat_dec_lt(v___x_989_, v___x_1011_);
if (v___x_1013_ == 0)
{
lean_dec_ref(v___y_982_);
v___y_912_ = v___y_984_;
v___y_913_ = v___x_1010_;
v_a_914_ = v___x_1012_;
goto v___jp_911_;
}
else
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_nat_dec_le(v___x_1011_, v___x_1011_);
if (v___x_1014_ == 0)
{
if (v___x_1013_ == 0)
{
lean_dec_ref(v___y_982_);
v___y_912_ = v___y_984_;
v___y_913_ = v___x_1010_;
v_a_914_ = v___x_1012_;
goto v___jp_911_;
}
else
{
size_t v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_usize_of_nat(v___x_1011_);
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_982_, v___x_995_, v___x_1015_, v___x_1012_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec_ref(v___y_982_);
v___y_942_ = v___y_984_;
v___y_943_ = v___x_1010_;
v___y_944_ = v___x_1016_;
goto v___jp_941_;
}
}
else
{
size_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_usize_of_nat(v___x_1011_);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_982_, v___x_995_, v___x_1017_, v___x_1012_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec_ref(v___y_982_);
v___y_942_ = v___y_984_;
v___y_943_ = v___x_1010_;
v___y_944_ = v___x_1018_;
goto v___jp_941_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_1006_);
lean_dec(v_a_1004_);
lean_dec_ref(v___y_982_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_1019_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1007_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1007_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_a_1004_);
lean_dec_ref(v___y_982_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_1027_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1005_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1005_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_val_1035_; lean_object* v___x_1037_; 
lean_dec_ref(v___y_982_);
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_val_1035_ = lean_ctor_get(v_fst_1001_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v_fst_1001_, 1);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_val_1035_);
v___x_1037_ = v___x_999_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_val_1035_);
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
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v___y_982_);
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_1040_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_996_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_996_);
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
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v___y_985_);
lean_dec_ref(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_1048_ = lean_ctor_get(v___y_986_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___y_986_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___y_986_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___y_986_);
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
v___jp_1056_:
{
lean_object* v_snd_1058_; lean_object* v_fst_1059_; lean_object* v_fst_1060_; lean_object* v_snd_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_snd_1058_ = lean_ctor_get(v_a_1057_, 1);
lean_inc(v_snd_1058_);
v_fst_1059_ = lean_ctor_get(v_a_1057_, 0);
lean_inc(v_fst_1059_);
lean_dec_ref(v_a_1057_);
v_fst_1060_ = lean_ctor_get(v_snd_1058_, 0);
lean_inc(v_fst_1060_);
v_snd_1061_ = lean_ctor_get(v_snd_1058_, 1);
lean_inc_n(v_snd_1061_, 2);
lean_dec(v_snd_1058_);
v___x_1062_ = l_Lean_Expr_cleanupAnnotations(v_snd_1061_);
v___x_1063_ = l_Lean_Expr_isApp(v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec_ref(v___x_1062_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_dec(v_fst_1059_);
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_e_796_);
goto v___jp_815_;
}
else
{
lean_object* v_arg_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_arg_1064_ = lean_ctor_get(v___x_1062_, 1);
lean_inc_ref(v_arg_1064_);
v___x_1065_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1062_);
v___x_1066_ = l_Lean_Expr_isApp(v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec_ref(v___x_1065_);
lean_dec_ref(v_arg_1064_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_dec(v_fst_1059_);
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_e_796_);
goto v___jp_815_;
}
else
{
lean_object* v_arg_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v_arg_1067_ = lean_ctor_get(v___x_1065_, 1);
lean_inc_ref(v_arg_1067_);
v___x_1068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1065_);
v___x_1069_ = l_Lean_Expr_isApp(v___x_1068_);
if (v___x_1069_ == 0)
{
lean_dec_ref(v___x_1068_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1064_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_dec(v_fst_1059_);
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_e_796_);
goto v___jp_815_;
}
else
{
lean_object* v_arg_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_arg_1070_ = lean_ctor_get(v___x_1068_, 1);
lean_inc_ref(v_arg_1070_);
v___x_1071_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1068_);
v___x_1072_ = l_Lean_Expr_isConstOf(v___x_1071_, v___x_843_);
lean_dec_ref(v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v_arg_1070_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1064_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_dec(v_fst_1059_);
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_e_796_);
goto v___jp_815_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_isExprDefEq(v_arg_841_, v_arg_1070_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; uint8_t v___x_1075_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
v___x_1075_ = lean_unbox(v_a_1074_);
lean_dec(v_a_1074_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1064_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
v___y_982_ = v_fst_1059_;
v___y_983_ = v_fst_1060_;
v___y_984_ = v___x_1072_;
v___y_985_ = v_snd_1061_;
v___y_986_ = v___x_1073_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1076_; 
lean_dec_ref_known(v___x_1073_, 1);
v___x_1076_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1072_, v_arg_1067_, v_arg_838_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; uint8_t v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = lean_unbox(v_a_1077_);
lean_dec(v_a_1077_);
if (v___x_1078_ == 0)
{
lean_dec_ref(v_arg_1064_);
lean_dec(v_fst_1060_);
lean_dec(v_fst_1059_);
lean_dec(v_a_980_);
lean_dec_ref(v_arg_835_);
v___y_955_ = v_snd_1061_;
goto v___jp_954_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1072_, v_arg_1064_, v_arg_835_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
v___y_982_ = v_fst_1059_;
v___y_983_ = v_fst_1060_;
v___y_984_ = v___x_1072_;
v___y_985_ = v_snd_1061_;
v___y_986_ = v___x_1079_;
goto v___jp_981_;
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v_arg_1064_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_dec(v_fst_1059_);
lean_dec(v_a_980_);
lean_dec(v_declName_845_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_e_796_);
v_a_1080_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1076_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1076_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1064_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
v___y_982_ = v_fst_1059_;
v___y_983_ = v_fst_1060_;
v___y_984_ = v___x_1072_;
v___y_985_ = v_snd_1061_;
v___y_986_ = v___x_1073_;
goto v___jp_981_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_declName_845_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_arg_835_);
lean_dec_ref(v_e_796_);
v_a_1156_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_979_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_979_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
v___jp_846_:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_796_, v___y_849_);
lean_dec_ref(v_e_796_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_add(v_a_860_, v___x_861_);
lean_dec(v_a_860_);
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_declName_845_);
v___x_864_ = lean_box(1);
v___x_865_ = l_Lean_Meta_Grind_addNewRawFact(v___y_848_, v___y_847_, v___x_862_, v___x_863_, v___x_864_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
return v___x_865_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v_declName_845_);
v_a_866_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_859_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_859_);
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
v___jp_874_:
{
if (v___y_877_ == 0)
{
lean_object* v_options_878_; uint8_t v_hasTrace_879_; 
v_options_878_ = lean_ctor_get(v___y_806_, 2);
v_hasTrace_879_ = lean_ctor_get_uint8(v_options_878_, sizeof(void*)*1);
if (v_hasTrace_879_ == 0)
{
v___y_847_ = v___y_875_;
v___y_848_ = v___y_876_;
v___y_849_ = v___y_798_;
v___y_850_ = v___y_799_;
v___y_851_ = v___y_800_;
v___y_852_ = v___y_801_;
v___y_853_ = v___y_802_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
goto v___jp_846_;
}
else
{
lean_object* v_inheritedTraceOptions_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_inheritedTraceOptions_880_ = lean_ctor_get(v___y_806_, 13);
v___x_881_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_882_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7);
v___x_883_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_880_, v_options_878_, v___x_882_);
if (v___x_883_ == 0)
{
v___y_847_ = v___y_875_;
v___y_848_ = v___y_876_;
v___y_849_ = v___y_798_;
v___y_850_ = v___y_799_;
v___y_851_ = v___y_800_;
v___y_852_ = v___y_801_;
v___y_853_ = v___y_802_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
goto v___jp_846_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_inc(v_declName_845_);
v___x_884_ = l_Lean_MessageData_ofName(v_declName_845_);
v___x_885_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
lean_inc_ref(v___y_875_);
v___x_887_ = l_Lean_MessageData_ofExpr(v___y_875_);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_881_, v___x_888_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_dec_ref_known(v___x_889_, 1);
v___y_847_ = v___y_875_;
v___y_848_ = v___y_876_;
v___y_849_ = v___y_798_;
v___y_850_ = v___y_799_;
v___y_851_ = v___y_800_;
v___y_852_ = v___y_801_;
v___y_853_ = v___y_802_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
goto v___jp_846_;
}
else
{
lean_dec_ref(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
return v___x_889_;
}
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec_ref(v___y_876_);
lean_dec_ref(v___y_875_);
v___x_890_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_802_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; uint8_t v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = lean_unbox(v_a_891_);
lean_dec(v_a_891_);
if (v___x_892_ == 0)
{
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
goto v___jp_809_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_893_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_894_ = l_Lean_MessageData_ofName(v_declName_845_);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_indentExpr(v_e_796_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_Meta_Sym_reportIssue(v___x_901_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_dec_ref_known(v___x_902_, 1);
goto v___jp_809_;
}
else
{
return v___x_902_;
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_903_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_890_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_890_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
v___jp_911_:
{
uint8_t v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; 
v___x_915_ = 0;
v___x_916_ = 1;
v___x_917_ = l_Lean_Meta_mkLambdaFVars(v_a_914_, v___y_913_, v___x_915_, v___y_912_, v___x_915_, v___y_912_, v___x_916_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec_ref(v_a_914_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_921_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_918_, v___y_805_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_n(v_a_920_, 2);
lean_dec_ref(v___x_919_);
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
v___x_921_ = lean_infer_type(v_a_920_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; uint8_t v___x_923_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v___x_923_ = l_Lean_Expr_hasMVar(v_a_920_);
if (v___x_923_ == 0)
{
uint8_t v___x_924_; 
v___x_924_ = l_Lean_Expr_hasMVar(v_a_922_);
v___y_875_ = v_a_922_;
v___y_876_ = v_a_920_;
v___y_877_ = v___x_924_;
goto v___jp_874_;
}
else
{
v___y_875_ = v_a_922_;
v___y_876_ = v_a_920_;
v___y_877_ = v___y_912_;
goto v___jp_874_;
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_a_920_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_925_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_921_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_921_);
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
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_933_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_917_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_917_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
v___jp_941_:
{
if (lean_obj_tag(v___y_944_) == 0)
{
lean_object* v_a_945_; 
v_a_945_ = lean_ctor_get(v___y_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___y_944_, 1);
v___y_912_ = v___y_942_;
v___y_913_ = v___y_943_;
v_a_914_ = v_a_945_;
goto v___jp_911_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v___y_943_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_946_ = lean_ctor_get(v___y_944_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___y_944_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___y_944_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___y_944_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
v___jp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_802_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; uint8_t v___x_958_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = lean_unbox(v_a_957_);
lean_dec(v_a_957_);
if (v___x_958_ == 0)
{
lean_dec_ref(v___y_955_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
goto v___jp_812_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_959_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_960_ = l_Lean_MessageData_ofName(v_declName_845_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_indentExpr(v_e_796_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_indentExpr(v___y_955_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_Meta_Sym_reportIssue(v___x_969_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_dec_ref_known(v___x_970_, 1);
goto v___jp_812_;
}
else
{
return v___x_970_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v___y_955_);
lean_dec(v_declName_845_);
lean_dec_ref(v_e_796_);
v_a_971_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_956_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_956_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
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
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_a_822_);
lean_dec_ref(v_thm_797_);
lean_dec_ref(v_e_796_);
v_a_1165_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_823_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_823_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_thm_797_);
lean_dec_ref(v_e_796_);
v_a_1173_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_821_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_821_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
v___jp_809_:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_box(0);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
v___jp_812_:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_box(0);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object* v_e_1181_, lean_object* v_thm_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(v_e_1181_, v_thm_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object* v_thm_1195_, lean_object* v_e_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___f_1208_; uint8_t v___x_1209_; lean_object* v___x_1210_; 
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed), 13, 2);
lean_closure_set(v___f_1208_, 0, v_e_1196_);
lean_closure_set(v___f_1208_, 1, v_thm_1195_);
v___x_1209_ = 0;
v___x_1210_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v___f_1208_, v___x_1209_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object* v_thm_1211_, lean_object* v_e_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_thm_1211_, v_e_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec(v_a_1213_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object* v_mvarId_1225_, lean_object* v_val_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_1225_, v_val_1226_, v___y_1234_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object* v_mvarId_1239_, lean_object* v_val_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(v_mvarId_1239_, v_val_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v___y_1241_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object* v_mvarId_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_1253_, v___y_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object* v_mvarId_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(v_mvarId_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v_mvarId_1266_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object* v_cls_1279_, lean_object* v_msg_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_1279_, v_msg_1280_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object* v_cls_1293_, lean_object* v_msg_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(v_cls_1293_, v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_1308_, v_x_1309_, v_x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object* v_00_u03b2_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1313_, v_x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(v_00_u03b2_1316_, v_x_1317_, v_x_1318_);
lean_dec(v_x_1318_);
lean_dec_ref(v_x_1317_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1321_, lean_object* v_x_1322_, size_t v_x_1323_, size_t v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1322_, v_x_1323_, v_x_1324_, v_x_1325_, v_x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
size_t v_x_217045__boxed_1334_; size_t v_x_217046__boxed_1335_; lean_object* v_res_1336_; 
v_x_217045__boxed_1334_ = lean_unbox_usize(v_x_1330_);
lean_dec(v_x_1330_);
v_x_217046__boxed_1335_ = lean_unbox_usize(v_x_1331_);
lean_dec(v_x_1331_);
v_res_1336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(v_00_u03b2_1328_, v_x_1329_, v_x_217045__boxed_1334_, v_x_217046__boxed_1335_, v_x_1332_, v_x_1333_);
return v_res_1336_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1337_, lean_object* v_x_1338_, size_t v_x_1339_, lean_object* v_x_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1338_, v_x_1339_, v_x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
size_t v_x_217062__boxed_1346_; uint8_t v_res_1347_; lean_object* v_r_1348_; 
v_x_217062__boxed_1346_ = lean_unbox_usize(v_x_1344_);
lean_dec(v_x_1344_);
v_res_1347_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(v_00_u03b2_1342_, v_x_1343_, v_x_217062__boxed_1346_, v_x_1345_);
lean_dec(v_x_1345_);
lean_dec_ref(v_x_1343_);
v_r_1348_ = lean_box(v_res_1347_);
return v_r_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03b2_1349_, lean_object* v_n_1350_, lean_object* v_k_1351_, lean_object* v_v_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_n_1350_, v_k_1351_, v_v_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_1354_, size_t v_depth_1355_, lean_object* v_keys_1356_, lean_object* v_vals_1357_, lean_object* v_heq_1358_, lean_object* v_i_1359_, lean_object* v_entries_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_1355_, v_keys_1356_, v_vals_1357_, v_i_1359_, v_entries_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1362_, lean_object* v_depth_1363_, lean_object* v_keys_1364_, lean_object* v_vals_1365_, lean_object* v_heq_1366_, lean_object* v_i_1367_, lean_object* v_entries_1368_){
_start:
{
size_t v_depth_boxed_1369_; lean_object* v_res_1370_; 
v_depth_boxed_1369_ = lean_unbox_usize(v_depth_1363_);
lean_dec(v_depth_1363_);
v_res_1370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_1362_, v_depth_boxed_1369_, v_keys_1364_, v_vals_1365_, v_heq_1366_, v_i_1367_, v_entries_1368_);
lean_dec_ref(v_vals_1365_);
lean_dec_ref(v_keys_1364_);
return v_res_1370_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_heq_1374_, lean_object* v_i_1375_, lean_object* v_k_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_1372_, v_i_1375_, v_k_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(lean_object* v_00_u03b2_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_heq_1381_, lean_object* v_i_1382_, lean_object* v_k_1383_){
_start:
{
uint8_t v_res_1384_; lean_object* v_r_1385_; 
v_res_1384_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(v_00_u03b2_1378_, v_keys_1379_, v_vals_1380_, v_heq_1381_, v_i_1382_, v_k_1383_);
lean_dec(v_k_1383_);
lean_dec_ref(v_vals_1380_);
lean_dec_ref(v_keys_1379_);
v_r_1385_ = lean_box(v_res_1384_);
return v_r_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11(lean_object* v_00_u03b2_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_x_1387_, v_x_1388_, v_x_1389_, v_x_1390_);
return v___x_1391_;
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
